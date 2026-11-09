-- Prove2me | Theorems.Thm_QueryDepthMIS_lemma_3_10
-- name    : QueryDepthMIS.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:33:32.641388+00:00
-- url     : https://prove2.me/theorems/3b7c054c-b580-4612-a19f-45586c6217c5
-- title:
--   Lemma 3.10 — w.h.p. no query path of $\lceil\sqrt A \log n\rceil$ vertices with positions in $(A\log n, \beta n)$
-- statement:
--   There exist constants $A > 0$ and $\beta > 0$ and an $n_0$ such that for every simple graph $G$ on $n \ge n_0$ vertices, with probability at least $1 - 1/n^6$ over a uniformly random permutation, every query path whose positions all lie strictly between $A \log n$ and $\beta n$ has fewer than
--   $$
--   \lceil \sqrt{A}\,\log n \rceil
--   $$
--   vertices ($\log$ to base 2).
--
--   This is the core of the proof of Theorem 3.1: it bounds query paths in the middle range of positions, where neither the degree reduction nor the short prefix applies.
--
--   Differences from the source:
--   - reading: absolute constants A, β → ∃ A β with 0 < A and 0 < β, chosen before n and G; reason: positivity is part of being such constants; β ≤ 0 would empty the window of positions
--   - reading: for all sufficiently large n → ∃ n₀, ∀ n ≥ n₀; reason: the phrase as printed
--   - encoding: a uniformly random permutation π of V, π(i) the i-th vertex → the uniform (counting) law on orderings ω : V ≃ Fin n, π = ω⁻¹, with 1-based ranks rank ω v = ω v + 1; reason: the same law; positions keep the paper's 1-based values
--   - encoding: a simple graph G with no order on V → an additional instance [LinearOrder V]; reason: required by the reused RGMISFast.tau to break rank ties; ranks of a permutation are injective, so it never acts
--   - encoding: a sequence of positions p₁ < ⋯ < p_L → the list of vertices at those positions, whose ranks are the positions; reason: positions and vertices correspond bijectively under rank
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 3.10, p.18

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_QueryDepthMIS_IsQueryPath
import Definitions.Def_QueryDepthMIS_rank

set_option autoImplicit false

namespace QueryDepthMIS

/-- Lemma 3.10 (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 3.10, p.18): "There exist absolute constants A, β such that, for all
sufficiently large n, with probability at least 1 − 1/n⁶, every query path whose positions lie
strictly between A log n and βn has fewer than ⌈√A log n⌉ vertices."

**Formalization Note** The constants are positive reals chosen before `n` and the graph ("for all
sufficiently large n" is `∃ n₀, ∀ n ≥ n₀`); a query path is a list of vertices, its positions are
their ranks, and its number of vertices is its length; `log` is `Real.logb 2`, and the root in
`⌈√A log n⌉` covers `A` only (p.14). -/
theorem lemma_3_10 :
    ∃ A β : ℝ, 0 < A ∧ 0 < β ∧ ∃ n₀ : ℕ,
    ∀ (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V →
      1 - 1 / (Fintype.card V : ℝ) ^ 6 ≤
        PunctSketch.coinProb (fun ω : Perm V => ∀ l : List V, IsQueryPath G (rank ω) l →
          (∀ v ∈ l, A * Real.logb 2 (Fintype.card V) < (rank ω v : ℝ) ∧
            (rank ω v : ℝ) < β * (Fintype.card V : ℝ)) →
          l.length < ⌈Real.sqrt A * Real.logb 2 (Fintype.card V)⌉₊) := by sorry

end QueryDepthMIS
