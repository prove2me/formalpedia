-- Prove2me | Theorems.Thm_SemiStreamMWM_theorem_1_1
-- name    : SemiStreamMWM.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:28:58.542227+00:00
-- url     : https://prove2.me/theorems/1e78038f-b965-445f-a3cc-c215d6a2452e
-- title:
--   Theorem 1.1 — deterministic semi-streaming $(1-\varepsilon)$-MCM in $O(\varepsilon^{-2})$ passes and $(1-\varepsilon)$-MWM in $O(\varepsilon^{-2}\log(1/\varepsilon))$ passes
-- statement:
--   Let $G$ be an $n$-vertex graph, read in the semi-streaming model: an algorithm makes passes over an arbitrary-order stream of the edges of $G$, on the word RAM, and is charged for every bit of memory it uses. Write $\mu(G)$ for the maximum matching cardinality and $\mu_w(G)$ for the maximum matching weight. There are deterministic semi-streaming algorithms for general graphs with the following guarantees, for every $0<\varepsilon\le1$:
--
--   1. a $(1-\varepsilon)$-MCM, i.e. a matching with at least $(1-\varepsilon)\mu(G)$ edges, using $$O(\varepsilon^{-2})\ \text{passes and}\ O\big(\mu(G)\,\varepsilon^{-2}\log n\big)\ \text{bits of space};$$
--   2. for integer edge weights in $[1,W]$ with $W=n^{O(1)}$, a $(1-\varepsilon)$-MWM, i.e. a matching of weight at least $(1-\varepsilon)\mu_w(G)$, using $$O\big(\varepsilon^{-2}\log(1/\varepsilon)\big)\ \text{passes and}\ O\big(\mu(G)\,\varepsilon^{-2}\log^2 n\big)\ \text{bits of space}.$$
--
--   Each algorithm is one program, fixed in advance, whose constants do not depend on $n$, $\varepsilon$, $W$, the graph or the edge order (in clause 2 they may depend on the exponent of the polynomial bound on $W$). This answers Assadi's question (SOSA 2024, Open Question 2) for unweighted matching and comes within a $\log(1/\varepsilon)$ factor of it for weighted matching; the previous bounds in general graphs were $O(\varepsilon^{-4})$ and $O(\varepsilon^{-39})$ passes.
--
--   Differences from the source:
--   - reading: deterministic semi-streaming algorithm on the standard word RAM with Θ(log n)-bit words → a `DynBrooks.Program` with no `coin` instruction, run by `passRun`, word size cw·ℓ(n + K) (clause 1) or cw·ℓ(n + K + W) (clause 2), with cw fixed before the instance; space w·|written| at every step; reason: the paper names the word RAM but no instruction set; all memory is charged (paper.md decisions 2–4)
--   - encoding: O(·) → A · (…), with P, cw, A before n, ε, W, the graph, the weights and the edge order (in clause 2 after κ only); reason: constants of a fixed algorithm (paper.md decision 5)
--   - encoding: µ(G), log n, log(1/ε) inside the bounds → µ(G) + 1, log₂(n + 2), log₂(2/ε); reason: same up to constant factors for n ≥ 2, µ ≥ 1, ε ≤ 1/2; the printed values are 0 at the degenerate points and would forbid reading the stream (paper.md decision 5)
--   - generalization: ε (the paper may assume ε = n^−O(1)) → every real ε ∈ (0, 1], given to the machine only as K = ⌈1/ε⌉; reason: the assumption on p.8 is a proof step; the statement specializes to the paper's ε (paper.md decision 6)
--   - reading: W = n^O(1) (footnote 1) → ∀ κ, W ≤ (n + 2)^κ, with the program and constants after κ; reason: for n ≥ 2, (n + 2)^κ ≤ n^{2κ}, so this is the paper's polynomial bound
--   - generalization: W ≥ 8 a power of two (footnote 1) → any integer W ≥ 1; reason: footnote 1 is a WLOG convention; the statement specializes to it (paper.md decision 6)
--   - encoding: word size Θ(log n) → word size cw·ℓ(n + K) and cw·ℓ(n + K + W); reason: equal up to constants for K, W ≤ n^O(1); larger words are charged in bits (paper.md decision 2)
--   - encoding: an arbitrary-order stream of edges; a matching as output → header, labels 1..n, sentinel 0, the same order in every pass; output as label pairs, not charged; reason: paper.md decisions 3, 7
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), Theorem 1.1, p.3 (restated p.18, proof p.21); semi-streaming model p.3; computational model p.8; footnote 1 p.3

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_StreamModel

open Classical

namespace SemiStreamMWM

/-- J. Chen, *Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General
Graphs: A Unified Framework* (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…),
Theorem 1.1, p.3 (restated p.18, proved p.21), with the model of p.3 and p.8 and footnote 1 (p.3).

"There are deterministic semi-streaming algorithms for general graphs with the following guarantees.
1. (1 − ε)-MCM using O(ε^−2) passes and O(µ(G)ε^−2 log n) bits of space.
2. (1 − ε)-MWM using O(ε^−2 log(1/ε)) passes and O(µ(G)ε^−2 log² n) bits of space."

**Formalization Note.** The model is `StreamModel`: a `DynBrooks.Program` on the word RAM,
deterministic = no `coin` instruction, word size `cw · ℓ(·)` with `cw` fixed before the instance, all
memory ever written charged, passes counted by re-delivering the same stream (arbitrary edge order, the
same in every pass) whenever the machine has read all of it and waits for more. Each `O` is a constant
`A` fixed with the program before `n`, `ε`, `W`, the graph, the weights and the edge order; in clause 2
the program and constants may depend on the exponent `κ` of `W ≤ (n + 2)^κ` (the paper's
`W = n^{O(1)}`, footnote 1), and on nothing else. `ε` is any real in `(0, 1]` and the machine receives
only `K = ⌈1/ε⌉`. Space is bounded at every step of the run, including after the last pass; the pass
count is the one at the halting step; the output decodes to a matching of `G` with at least
`(1 − ε)µ(G)` edges, or of weight at least `(1 − ε)µ_w(G)`. Weights are integers in `[1, W]` for any
`W ≥ 1`. Inside the bounds `µ(G)` is `µ(G) + 1`, `log n` is `log₂(n + 2)` and `log(1/ε)` is `log₂(2/ε)`,
equal to the printed expressions up to constant factors wherever those are nonzero. -/
theorem theorem_1_1 :
    (∃ (P : DynBrooks.Program) (cw : ℕ) (A : ℝ), IsDeterministic P ∧
      ∀ (n : ℕ) (ε : ℝ) (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)),
        0 < ε → ε ≤ 1 → IsEdgeStream G es →
        let K := ⌈1 / ε⌉₊
        let w := cw * ell (n + K)
        let inp := mcmWords K es
        (∀ t, (spaceBits w (passRun P w inp t).1 : ℝ) ≤
          A * ((mcm G : ℝ) + 1) / ε ^ 2 * Real.logb 2 ((n : ℝ) + 2)) ∧
        ∃ t, IsHalted P (passRun P w inp t).1 ∧ ((passRun P w inp t).2 : ℝ) ≤ A / ε ^ 2 ∧
          ∃ M, decodePairs n (passRun P w inp t).1.output = some M ∧ IsMatchingList G M ∧
            (1 - ε) * (mcm G : ℝ) ≤ M.length) ∧
    (∀ κ : ℕ, ∃ (P : DynBrooks.Program) (cw : ℕ) (A : ℝ), IsDeterministic P ∧
      ∀ (n W : ℕ) (ε : ℝ) (G : SimpleGraph (Fin n)) (wt : Sym2 (Fin n) → ℕ)
        (es : List (Fin n × Fin n)),
        0 < ε → ε ≤ 1 → 1 ≤ W → W ≤ (n + 2) ^ κ → (∀ e ∈ G.edgeSet, 1 ≤ wt e ∧ wt e ≤ W) →
        IsEdgeStream G es →
        let K := ⌈1 / ε⌉₊
        let w := cw * ell (n + K + W)
        let inp := mwmWords W K wt es
        (∀ t, (spaceBits w (passRun P w inp t).1 : ℝ) ≤
          A * ((mcm G : ℝ) + 1) / ε ^ 2 * Real.logb 2 ((n : ℝ) + 2) ^ 2) ∧
        ∃ t, IsHalted P (passRun P w inp t).1 ∧
          ((passRun P w inp t).2 : ℝ) ≤ A / ε ^ 2 * Real.logb 2 (2 / ε) ∧
          ∃ M, decodePairs n (passRun P w inp t).1.output = some M ∧ IsMatchingList G M ∧
            (1 - ε) * (mwm G wt : ℝ) ≤ listWeight wt M) := by sorry

end SemiStreamMWM
