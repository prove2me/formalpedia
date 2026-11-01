-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_pointwiseSummable_subfamily
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.pointwiseSummable_subfamily
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:24:04.045231+00:00
-- url     : https://prove2.me/theorems/a69d21bd-2645-4661-996d-fc8464890d32
-- title:
--   Lemma A.1
-- statement:
--   Let $X$ be a topological space, $I$ any index set, and $V$ a complete Hausdorff abelian topological group, equipped with its compatible group uniformity. Let $\phi_i:X\to V$ be a pointwise unconditionally summable family: at each $x$ the net of finite partial sums converges. Then
--
--   $$\forall J\subseteq I\;\forall x\in X,\qquad\sum_{j\in J}\phi_j(x)\text{ converges in }V.$$
--
--   In particular every subfamily is pointwise summable, including the empty subfamily, whose sum is zero. Continuity of the individual functions or of the sums is not asserted.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 32, Lemma A.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Lemma A.1, PDF pp. 32–33: pointwise unconditional summability is
inherited by every subfamily in a complete Hausdorff abelian group. -/
theorem pointwiseSummable_subfamily
    (X : Type u) [TopologicalSpace X] (I : Type v)
    (V : Type u) [AddCommGroup V] [UniformSpace V] [IsUniformAddGroup V]
    [CompleteSpace V] [T2Space V] (phi : I → X → V)
    (hphi : ∀ x, Summable (fun i => phi i x)) :
    ∀ (J : Set I) (x : X), Summable (fun j : J => phi j.val x) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
