-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_adicAbv_of_intValuation_eq_ca2fe8961340
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_adicAbv_of_intValuation_eq_ca2fe8961340
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:13.571771+00:00
-- url     : https://prove2.me/theorems/bd2920ef-777d-5408-91db-bda10e9cd2d4
-- title:
--   P2 M Ground Theory Heights  Heights Vertical adic Abv of int Valuation eq ca2fe8961340: P2 M Ground Theory Heights  Heights Vertical adic Abv of int Valuation eq ca2fe8961340
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical adic Abv of int Valuation eq ca2fe8961340 construction uses the P2 M Ground Theory Heights  Heights Vertical adic Abv of int Valuation eq ca2fe8961340 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGaussDVR.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGaussDVR.lean#L63-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGaussDVR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain WithZero
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_Vertical_adicAbv_of_intValuation_eq_ca2fe8961340 (v : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K}
    (ha : v.intValuation a = exp (-1 : ℤ)) :
    NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K a) =
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«adicAbv_of_intValuation_eq» := P2M_GroundTheory_Heights__Heights_Vertical_adicAbv_of_intValuation_eq_ca2fe8961340
