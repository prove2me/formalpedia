-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_integral_fin_zero_ff47667ab96f
-- name    : P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_integral_fin_zero_ff47667ab96f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:16:58.001579+00:00
-- url     : https://prove2.me/theorems/23f27be3-0ece-4fb2-8429-87f7fc1c5860
-- title:
--   P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux integral fin zero ff47667ab96f: P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux integral fin zero ff47667ab96f
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux integral fin zero ff47667ab96f construction uses the P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux integral fin zero ff47667ab96f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPtsIntegralZeroLowerNE.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPtsIntegralZeroLowerNE.lean#L44-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPtsIntegralZeroLowerNE
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.PtsIntegralZeroLowerNEAux
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_integral_fin_zero_ff47667ab96f (F : (Fin 0 → ℂ) → ℝ) (y : Fin 0 → ℂ) : ∫ y', F y' = F y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsIntegralZeroLowerNEAux».«integral_fin_zero» := P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_integral_fin_zero_ff47667ab96f
