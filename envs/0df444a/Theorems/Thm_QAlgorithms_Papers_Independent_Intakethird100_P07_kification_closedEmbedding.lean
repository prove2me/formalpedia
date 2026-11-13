-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kification_closedEmbedding
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.kification_closedEmbedding
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T04:28:11.474059+00:00
-- url     : https://prove2.me/theorems/1f0efb68-5c13-4213-a014-edcb5ac6e35a
-- title:
--   Lemma B.10
-- statement:
--   Let $f:X\to Y$ be a closed embedding between arbitrary topological spaces. Give $kX$ and $kY$ the final topologies for their compact Hausdorff probes. Then
--
--   $$k(f):kX\longrightarrow kY,\qquad k(f)(x)=f(x),$$
--
--   is a closed embedding. This preserves the original underlying map and asserts the embedding property as well as closedness of its image.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 37, Lemma B.10

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Lemma B.10, PDF p. 37: k preserves closed embeddings, for the same
underlying map, with final probe topologies on its domain and codomain. -/
theorem kification_closedEmbedding
    (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsClosedEmbedding f) :
    @IsClosedEmbedding (KSpace X) (KSpace Y) _ _ f := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
