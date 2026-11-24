-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_hypotheses_inhabited_687dc14d1232
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_hypotheses_inhabited_687dc14d1232
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:22.610563+00:00
-- url     : https://prove2.me/theorems/edc2dae8-914e-48d9-9651-3ff53a6b5239
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 hypotheses inhabited 687dc14d1232: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 hypothese
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 hypotheses inhabited 687dc14d1232 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 hypotheses inhabited 687dc14d1232 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardInnerSingleNe.lean#L65-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardInnerSingleNe.lean#L65-L78

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_hypotheses_inhabited_687dc14d1232 :
    DirectSum.IsInternal (coordLines ℚ) ∧
      (∀ x, (HermitianBundle.standard ℚ 2).rank (coordLines ℚ x) = 1) ∧
      IsOrthogonalFamily (HermitianBundle.standard ℚ 2) (coordLines ℚ) ∧
      (∀ x, min ((HermitianBundle.standard ℚ 2).normDegree (coordLines ℚ 0))
          ((HermitianBundle.standard ℚ 2).normDegree (coordLines ℚ 1)) ≤
        (HermitianBundle.standard ℚ 2).normDegree (coordLines ℚ x)) ∧
      Nonempty (HermitianExtension (HermitianBundle.integers ℚ) (HermitianBundle.standard ℚ 2)
        (HermitianBundle.integers ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«S6».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_hypotheses_inhabited_687dc14d1232
