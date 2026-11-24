-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ae_fibreCount_eq_zero_40bf10712179
-- name    : P2M_GroundTheory_Heights__Heights_ae_fibreCount_eq_zero_40bf10712179
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:53.153458+00:00
-- url     : https://prove2.me/theorems/0438e8ef-6820-4e44-b3eb-321e4aaf7012
-- title:
--   P2 M Ground Theory Heights  Heights ae fibre Count eq zero 40bf10712179: P2 M Ground Theory Heights  Heights ae fibre Count eq zero 40bf10712179
-- statement:
--   The P2 M Ground Theory Heights  Heights ae fibre Count eq zero 40bf10712179 construction uses the P2 M Ground Theory Heights  Heights ae fibre Count eq zero 40bf10712179 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeIntegralMass.lean#L77-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeIntegralMass.lean#L77-L91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
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
open MvPolynomial MeasureTheory Module
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ae_fibreCount_eq_zero_40bf10712179 {n m : ℕ} (hnm : n < m) (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (π : Fin m → Fin n → ℂ) :
    ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ae_fibreCount_eq_zero» := P2M_GroundTheory_Heights__Heights_ae_fibreCount_eq_zero_40bf10712179
