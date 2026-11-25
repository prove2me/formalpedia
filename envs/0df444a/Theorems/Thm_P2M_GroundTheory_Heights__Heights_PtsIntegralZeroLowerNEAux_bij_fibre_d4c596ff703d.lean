-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_bij_fibre_d4c596ff703d
-- name    : P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_bij_fibre_d4c596ff703d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:53.194789+00:00
-- url     : https://prove2.me/theorems/fb1e2ec6-3696-44cd-a132-9e99c99c7c49
-- title:
--   P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux bij fibre d4c596ff703d: P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux bij fibre d4c596ff703d
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux bij fibre d4c596ff703d construction uses the P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux bij fibre d4c596ff703d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPtsIntegralZeroLowerNE.lean#L68-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPtsIntegralZeroLowerNE.lean#L68-L122

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

theorem P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_bij_fibre_d4c596ff703d [Nonempty K] {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)) (hΨ : IsGoodProj W Ψ) (y : Fin 0 → ℂ) :
    ∃ M : McClasses W → fibre W Ψ y, Function.Bijective M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsIntegralZeroLowerNEAux».«bij_fibre» := P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_bij_fibre_d4c596ff703d
