-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kification_openEmbedding
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.kification_openEmbedding
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T04:28:35.657643+00:00
-- url     : https://prove2.me/theorems/5b07cc36-4e27-45c5-be23-0faae4096398
-- title:
--   Lemma B.12
-- statement:
--   Let $f:X\to Y$ be an open embedding between arbitrary topological spaces. Kification preserves this embedding:
--
--   $$k(f):kX\longrightarrow kY,\qquad k(f)(x)=f(x),\quad\text{is an open embedding}.$$
--
--   Here kification is the final compact-Hausdorff-probe topology. Neither source nor target is assumed Hausdorff.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 37, Lemma B.12

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Lemma B.12, PDF p. 37: k preserves open embeddings, without a
separation hypothesis on either topological space. -/
theorem kification_openEmbedding
    (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsOpenEmbedding f) :
    @IsOpenEmbedding (KSpace X) (KSpace Y) _ _ f := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
