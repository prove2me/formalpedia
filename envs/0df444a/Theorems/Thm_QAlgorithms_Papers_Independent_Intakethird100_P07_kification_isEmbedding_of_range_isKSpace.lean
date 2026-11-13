-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kification_isEmbedding_of_range_isKSpace
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.kification_isEmbedding_of_range_isKSpace
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T23:11:16.319419+00:00
-- url     : https://prove2.me/theorems/75ba06a0-1bcd-4156-89e5-8a15b6e3e3dd
-- title:
--   Kification preserves embeddings with compactly generated range
-- statement:
--   Let f:X→Y be a topological embedding between arbitrary spaces in the same universe. If its image, with the subspace topology inherited from kY, is compactly generated, then the same function is an embedding $$kX\hookrightarrow kY.$$ No Hausdorff or open/closed image assumption is required; the sufficient condition on the image is stated explicitly. This is a reusable intermediate form of the image-subspace argument for preservation of open and closed embeddings.
-- source:
--   Martin Fuchssteiner, Cohomology of Local Cochains, arXiv:1110.2661v2, https://arxiv.org/pdf/1110.2661v2, Reusable intermediate form of the proofs of Lemmas B.10 and B.12, PDF p.37; the source applies the range condition to closed and open subspaces respectively.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07
import Mathlib.Topology.Homeomorph.Lemmas
noncomputable section
universe u
open CategoryTheory Topology TopologicalSpace Set

namespace QAlgorithms.Papers.Independent.Intakethird100.P07
theorem kification_isEmbedding_of_range_isKSpace
    (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsEmbedding f)
    (hR : UCompactlyGeneratedSpace.{u} {y : KSpace Y // y ∈ Set.range f}) :
    @IsEmbedding (KSpace X) (KSpace Y) _ _ f := by sorry
end QAlgorithms.Papers.Independent.Intakethird100.P07
