-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_pointwiseSummable_absolute
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.pointwiseSummable_absolute
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:24:39.79602+00:00
-- url     : https://prove2.me/theorems/9983233c-46b8-4701-abb8-99988b450027
-- title:
--   Lemma A.2
-- statement:
--   Let $X$ be a topological space and $(\phi_i:X\to\mathbb R)_{i\in I}$ a family whose finite partial sums converge at every point. Then its absolute-value family is pointwise summable:
--
--   $$\forall x\in X,\qquad\sum_{i\in I}|\phi_i(x)|\text{ converges in }\mathbb R.$$
--
--   The sums are unconditional, indexed by finite subsets of $I$. This is an existence statement about pointwise sums, without a continuity or local uniform convergence conclusion.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 33, Lemma A.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Lemma A.2, PDF p. 33: the absolute-value family is pointwise summable.
There is no continuity or local uniform convergence assertion here. -/
theorem pointwiseSummable_absolute
    (X : Type u) [TopologicalSpace X] (I : Type v) (phi : I → X → ℝ)
    (hphi : ∀ x, Summable (fun i => phi i x)) :
    ∀ x, Summable (fun i => |phi i x|) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
