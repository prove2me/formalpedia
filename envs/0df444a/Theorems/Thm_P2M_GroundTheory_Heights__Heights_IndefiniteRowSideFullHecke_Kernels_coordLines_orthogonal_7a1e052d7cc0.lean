-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_orthogonal_7a1e052d7cc0
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_orthogonal_7a1e052d7cc0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:57.887302+00:00
-- url     : https://prove2.me/theorems/1c4fe489-6c94-4642-b7db-2ee8b1a09f74
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels coord Lines orthogonal 7a1e052d7cc0: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels coord Lines o
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels coord Lines orthogonal 7a1e052d7cc0 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels coord Lines orthogonal 7a1e052d7cc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardInnerSingleNe.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardInnerSingleNe.lean#L58-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField TensorProduct GroundTheory.Heights₂.Heights
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_orthogonal_7a1e052d7cc0 (K : Type*) [Field K] [NumberField K] :
    IsOrthogonalFamily (HermitianBundle.standard K 2) (coordLines K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«coordLines_orthogonal» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_orthogonal_7a1e052d7cc0
