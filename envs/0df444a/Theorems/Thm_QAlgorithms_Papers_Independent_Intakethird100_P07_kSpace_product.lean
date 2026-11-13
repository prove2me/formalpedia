-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kSpace_product
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.kSpace_product
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T04:27:06.553196+00:00
-- url     : https://prove2.me/theorems/2622a5cf-6e64-4451-863c-d1ef0b2fe9e7
-- title:
--   Proposition B.8
-- statement:
--   Let $(Y_i)_{i\in I}$ be any family of compactly Hausdorff generated spaces. Its product in kTop is the kification of the ordinary topological product:
--
--   $$\prod_{i\in I}^{\mathrm{kTop}}Y_i=k\!\left(\prod_{i\in I}^{\mathrm{Top}}Y_i\right),\qquad\pi_i((y_j)_j)=y_i.$$
--
--   The formal conclusion says that this specific cone, including its displayed projection maps, is a limit cone. It also includes the empty family.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 36, Proposition B.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Proposition B.8, PDF p. 36: the concrete kified product cone is limiting,
including its canonical projection maps. The empty family is allowed. -/
theorem kSpace_product (I : Type u) (Y : I → CompactlyGenerated.{u, u}) :
    Nonempty (Limits.IsLimit (kProductCone Y)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
