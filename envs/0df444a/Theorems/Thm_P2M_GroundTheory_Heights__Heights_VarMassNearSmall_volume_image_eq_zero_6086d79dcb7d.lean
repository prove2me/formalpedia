-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarMassNearSmall_volume_image_eq_zero_6086d79dcb7d
-- name    : P2M_GroundTheory_Heights__Heights_VarMassNearSmall_volume_image_eq_zero_6086d79dcb7d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:41:54.199741+00:00
-- url     : https://prove2.me/theorems/8f398b81-8f65-410f-a5ed-f30eef57b5cd
-- title:
--   P2 M Ground Theory Heights  Heights Var Mass Near Small volume image eq zero 6086d79dcb7d: P2 M Ground Theory Heights  Heights Var Mass Near Small volume image eq zero 6086d79dcb7d
-- statement:
--   The P2 M Ground Theory Heights  Heights Var Mass Near Small volume image eq zero 6086d79dcb7d construction uses the P2 M Ground Theory Heights  Heights Var Mass Near Small volume image eq zero 6086d79dcb7d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarMassNearSmall.lean#L50-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarMassNearSmall.lean#L50-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarMassNearSmall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal NNReal
noncomputable section
open GroundTheory.Heights₂.Heights.VarMassNearSmall
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_VarMassNearSmall_volume_image_eq_zero_6086d79dcb7d (W I : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hI : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < d) :
    volume (A.mulVec '' (zeroSet W ∩ zeroSet I)) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarMassNearSmall».«volume_image_eq_zero» := P2M_GroundTheory_Heights__Heights_VarMassNearSmall_volume_image_eq_zero_6086d79dcb7d
