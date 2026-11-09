-- Prove2me | Theorems.Thm_SemiStreamMWM_lemma_1_6
-- name    : SemiStreamMWM.lemma_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:19:26.873373+00:00
-- url     : https://prove2.me/theorems/149d1142-1d39-4ab9-b978-c0686c7000d4
-- title:
--   Lemma 1.6 [GW19] — a one-pass deterministic $1/4$-MWM in $O(\mu(G)\log W\log n)$ bits
-- statement:
--   In the multi-pass semi-streaming model of the mission (word RAM, all written memory charged): for every exponent $\kappa$ there is one deterministic program which, for every $n$-vertex graph $G$ with integer edge weights in $[1,W]$, $1\le W\le(n+2)^\kappa$, and every order of its edge stream, halts after a single pass with a matching $M$ of $G$ satisfying
--
--   $$w(M)\ge\tfrac14\,\mu_w(G),$$
--
--   using at every step at most $O\big(\mu(G)\log W\log n\big)$ bits of space, with the constant depending only on $\kappa$.
--
--   The algorithm computes the estimate $L$ of Algorithm 2.2 and the crossing matching of the streaming step oracle.
--
--   Differences from the source:
--   - reading: an algorithm on the standard word RAM with Θ(log n)-bit words, in one pass, deterministically → a `DynBrooks.Program` with no `coin` instruction, word size cw·ℓ(n + W), started with the stream pending, halting with pass count ≤ 1; space w·|written| at every step; reason: the paper names the word RAM but no instruction set; all memory is charged (paper.md decisions 2–4)
--   - reading: W bounded by n^O(1) (footnote 1) → ∀ κ, W ≤ (n + 2)^κ, with P, cw, A chosen after κ; reason: footnote 1 is a standing assumption of the paper; the proof's O(log n)-bit records use it
--   - generalization: W ≥ 8 a power of two (footnote 1) → any integer W ≥ 1; reason: footnote 1 is a convention; the statement specializes to it
--   - encoding: O(µ(G) log W log n) → A·(µ(G) + 1)·log₂(W + 1)·log₂(n + 2) with A fixed before the instance; reason: equal up to a constant factor whenever the printed value is nonzero; at µ = 0 or W = 1 the printed value 0 would forbid reading the stream
--   - encoding: the edge stream → header n, W, then each edge as two labels in 1..n and its weight, then the sentinel 0; output as label pairs, not charged; reason: paper.md decisions 3, 7
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), Lemma 1.6 ([GW19]), p.8; footnote 1 p.3

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_StreamModel

open Classical

namespace SemiStreamMWM

/-- J. Chen (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), Lemma 1.6 ([GW19]), p.8,
in the model of p.3 and p.8 and under footnote 1 (p.3), `W` bounded by `n^{O(1)}`.

"Given an edge stream of a graph with weights in [1, W], a 1/4-MWM can be computed deterministically
in one pass using O(µ(G) log W log n) bits of space."

**Formalization Note.** The machine, passes, space and output are those of `StreamModel`. One
deterministic program `P`, a word-size factor `cw` and the `O`-constant `A` come after the exponent
`κ` of the polynomial weight bound `W ≤ (n + 2)^κ` and before `n`, `W`, the graph, the weights and the
edge order. The word size is `cw · ℓ(n + W)`. Each pass delivers `n`, `W`, then each edge as two labels
in `1..n` and its weight, then `0`. Space is bounded at every step of the run; the run halts having
started at most one pass, and outputs a matching of weight at least `µ_w(G)/4`. In the space bound
`µ(G)` is `µ(G) + 1`, `log W` is `log₂(W + 1)` and `log n` is `log₂(n + 2)`, which differ from the
printed expressions only by constant factors where those are nonzero. -/
theorem lemma_1_6 : ∀ κ : ℕ, ∃ (P : DynBrooks.Program) (cw : ℕ) (A : ℝ), IsDeterministic P ∧
    ∀ (n W : ℕ) (G : SimpleGraph (Fin n)) (wt : Sym2 (Fin n) → ℕ) (es : List (Fin n × Fin n)),
      1 ≤ W → W ≤ (n + 2) ^ κ → (∀ e ∈ G.edgeSet, 1 ≤ wt e ∧ wt e ≤ W) → IsEdgeStream G es →
      let w := cw * ell (n + W)
      let inp := gwWords W wt es
      (∀ t, (spaceBits w (passRun P w inp t).1 : ℝ) ≤
        A * ((mcm G : ℝ) + 1) * Real.logb 2 ((W : ℝ) + 1) * Real.logb 2 ((n : ℝ) + 2)) ∧
      ∃ t, IsHalted P (passRun P w inp t).1 ∧ (passRun P w inp t).2 ≤ 1 ∧
        ∃ M, decodePairs n (passRun P w inp t).1.output = some M ∧ IsMatchingList G M ∧
          mwm G wt ≤ 4 * listWeight wt M := by sorry

end SemiStreamMWM
