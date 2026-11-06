-- Prove2me | Theorems.Thm_TIESched_lemma_5_7
-- name    : TIESched.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:47:36.357235+00:00
-- url     : https://prove2.me/theorems/e9c3d741-88e7-43a5-ae9f-ecc4c67296f2
-- title:
--   Lemma 5.7 — zero boundary condition for utility interactions
-- statement:
--   Let $(x,u)$ be a feasible, truthful, padding-invariant fractional mechanism family. For every finite job set $J$, every nonnegative report $p_J$ and every machine $i$,
--   $$p_{ik}=0\ \text{for some }k\in J\ \Longrightarrow\ V^J_i(p_J)=0,$$
--   where $V^J_i$ is the utility interaction of $(x,u)$.
--
--   Differences from the source:
--   - reading: padding-invariant (T_v defined with one chosen fresh label per job set) → invariance for every fresh label k ∉ S; reason: the proof of Lemma 5.7 (p.25) views a job k ∈ J as the padding job of S∖{k}, which needs invariance for that label; the family of Lemma 5.6 is relabeling-equivariant, so the choice is immaterial (p.24)
--   - encoding: rules x^S, π^S on ℝ^{m×S}_{≥0} with values in X(S) → total functions on ℝ^{m×S}, with feasibility a separate predicate on nonnegative reports; reason: a family on the orthant extends to such a total function, and the hypotheses read nonnegative reports only
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Lemma 5.7, p.25

import Mathlib
import Definitions.Def_TIESched_PaddingInvariant
import Definitions.Def_TIESched_utilityInteraction

set_option autoImplicit false

namespace TIESched

/-- **Lemma 5.7 (Zero boundary condition)** (Wang, Xu, Zhang, arXiv:2611.05142, Lemma 5.7, p.25).
Let `(x, u)` be a padding-invariant truthful fractional mechanism family. For every finite job set
`J`, every nonnegative report `p_J`, and every machine `i`:
`p_ik = 0` for some `k ∈ J` implies `V^J_i(p_J) = 0`, where `V^J_i` is the utility interaction. -/
theorem lemma_5_7 (m : ℕ) [NeZero m] (hm : 2 ≤ m) (M : FracMech m) (hfeas : Feasible M.alloc)
    (htr : Truthful M) (hpad : PaddingInvariant M) (J : Finset ℕ) (p : Fin m → J → ℝ)
    (hp : IsNonneg p) (i : Fin m) (hk : ∃ k : J, p i k = 0) :
    utilityInteraction M J p i = 0 := by sorry

end TIESched
