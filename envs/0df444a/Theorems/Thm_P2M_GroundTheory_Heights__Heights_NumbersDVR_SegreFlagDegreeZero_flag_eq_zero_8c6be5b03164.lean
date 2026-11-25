-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagDegreeZero_flag_eq_zero_8c6be5b03164
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagDegreeZero_flag_eq_zero_8c6be5b03164
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:08:44.654842+00:00
-- url     : https://prove2.me/theorems/cbadb8ad-4ef1-45ed-b919-6d6deefd5d8f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Degree Zero flag eq zero 8c6be5b03164: P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Degree Zero flag eq zero 8c6be5b03164
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Degree Zero flag eq zero 8c6be5b03164 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Degree Zero flag eq zero 8c6be5b03164 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/AevalEqOfVdeg.lean#L39-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/AevalEqOfVdeg.lean#L39-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AevalEqOfVdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagDegreeZero

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagDegreeZero_flag_eq_zero_8c6be5b03164 {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N : ℕ} (w e : Module.Basis (Fin N) Ω E)
    {t : Fin N → Φ} (ht : LinearIndependent Ω t) (χ : Module.Dual Ω E) {k : ℕ}
    (h0 : ∑ j, flagCoord w e t k j * algebraMap Ω Φ (χ (w j)) = 0) (j : Fin N) (hj : (j : ℕ) < k) :
    χ (w j) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SegreFlagDegreeZero».«flag_eq_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagDegreeZero_flag_eq_zero_8c6be5b03164
