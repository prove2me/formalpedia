-- Prove2me | Theorems.Thm_SemiStreamMWM_lemma_4_4
-- name    : SemiStreamMWM.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:19:25.273671+00:00
-- url     : https://prove2.me/theorems/963e3aa7-5c5e-4f13-9248-efe585702b93
-- title:
--   Lemma 4.4 — a deterministic $(1-\varepsilon)$-MWM in $O(\log W/\varepsilon^2)$ passes and $O(\mu(G)\varepsilon^{-2}\log W\log n)$ bits
-- statement:
--   In the multi-pass semi-streaming model of the mission: for every exponent $\kappa$ there is one deterministic program (Algorithm 4.2) which, for every $n$-vertex graph $G$ with integer edge weights in $[1,W]$, where $W\ge8$ is a power of two with $W\le(n+2)^\kappa$, every $0<\varepsilon\le1$ (given to the program as $K=\lceil1/\varepsilon\rceil$) and every order of the edge stream, halts with a matching $M$ of $G$ with
--
--   $$w(M)\ge(1-\varepsilon)\,\mu_w(G),$$
--
--   using $O(\log W/\varepsilon^2)$ passes and, at every step, $O\big(\mu(G)\varepsilon^{-2}\log W\log n\big)$ bits of space, with constants depending only on $\kappa$.
--
--   This is the streaming implementation of the framework of §2, before the weight reduction of Lemma 4.5.
--
--   Differences from the source:
--   - reading: Algorithm 4.2 computes … → there is one deterministic program (no `coin` instruction) that computes …; reason: Algorithm 4.2 is pseudo-code over cited routines, not a Lean object (paper.md decision 8)
--   - reading: the standard word RAM with Θ(log n)-bit words; passes over an arbitrary-order stream → a `DynBrooks.Program`, word size cw·ℓ(n + K + W), passes counted by re-delivering the same stream, space w·|written| at every step; reason: the paper names no instruction set; all memory is charged (paper.md decisions 2–3)
--   - reading: W bounded by n^O(1) (footnote 1) → ∀ κ, W ≤ (n + 2)^κ, with P, cw, A chosen after κ; reason: footnote 1 is a standing assumption of the paper
--   - generalization: ε (the paper may assume ε = n^−O(1)) → every real ε ∈ (0, 1], given to the machine only as K = ⌈1/ε⌉; reason: the assumption on p.8 is a proof step; the statement specializes to the paper's ε
--   - encoding: O(µ(G)ε^−2 log W log n) bits and O(log W/ε²) passes → A·(µ(G) + 1)/ε²·log₂W·log₂(n + 2) and A·log₂W/ε², A fixed before the instance; reason: equal up to constant factors whenever the printed value is nonzero
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), Lemma 4.4, p.20; Algorithm 4.2, p.20; footnote 1 p.3

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_StreamModel

open Classical

namespace SemiStreamMWM

/-- J. Chen (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), Lemma 4.4, p.20, in the model
of p.3 and p.8 and under footnote 1 (p.3): `W ≥ 8` a power of two bounded by `n^{O(1)}`.

"Algorithm 4.2 computes a (1 − ε)-MWM using O(µ(G)ε^−2 log W log n) bits of space and O(log W/ε²)
passes."

**Formalization Note.** Algorithm 4.2 (p.20) is pseudo-code over Algorithms 2.1, 2.2, 4.1 and the
cited routines; the lemma is stated as the existence of one deterministic program (Algorithm 4.2 is
deterministic) meeting its bounds. `P`, the word-size factor `cw` and the `O`-constant `A` come after
`κ` (`W ≤ (n + 2)^κ`) and before `n`, `W`, `ε`, the graph, the weights and the edge order. The machine
receives `ε` only as `K = ⌈1/ε⌉`, in the header `n, W, K`; the approximation is against the real `ε`,
for every `ε ∈ (0, 1]`. The word size is `cw · ℓ(n + K + W)`. Space is bounded at every step;
the pass count is the one at the halting step. `µ(G)` in the space bound is `µ(G) + 1` and `log n` is
`log₂(n + 2)`; `log W ≥ 3`. -/
theorem lemma_4_4 : ∀ κ : ℕ, ∃ (P : DynBrooks.Program) (cw : ℕ) (A : ℝ), IsDeterministic P ∧
    ∀ (n W : ℕ) (ε : ℝ) (G : SimpleGraph (Fin n)) (wt : Sym2 (Fin n) → ℕ)
      (es : List (Fin n × Fin n)),
      0 < ε → ε ≤ 1 → 8 ≤ W → (∃ j : ℕ, W = 2 ^ j) → W ≤ (n + 2) ^ κ →
      (∀ e ∈ G.edgeSet, 1 ≤ wt e ∧ wt e ≤ W) → IsEdgeStream G es →
      let K := ⌈1 / ε⌉₊
      let w := cw * ell (n + K + W)
      let inp := mwmWords W K wt es
      (∀ t, (spaceBits w (passRun P w inp t).1 : ℝ) ≤
        A * ((mcm G : ℝ) + 1) / ε ^ 2 * Real.logb 2 W * Real.logb 2 ((n : ℝ) + 2)) ∧
      ∃ t, IsHalted P (passRun P w inp t).1 ∧
        ((passRun P w inp t).2 : ℝ) ≤ A * Real.logb 2 W / ε ^ 2 ∧
        ∃ M, decodePairs n (passRun P w inp t).1.output = some M ∧ IsMatchingList G M ∧
          (1 - ε) * (mwm G wt : ℝ) ≤ listWeight wt M := by sorry

end SemiStreamMWM
