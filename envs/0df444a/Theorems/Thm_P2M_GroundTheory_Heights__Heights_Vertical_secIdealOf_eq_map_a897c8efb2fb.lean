-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_secIdealOf_eq_map_a897c8efb2fb
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_secIdealOf_eq_map_a897c8efb2fb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:24.058879+00:00
-- url     : https://prove2.me/theorems/af176e4c-3e98-4a8b-998e-e00d1cbcdfbe
-- title:
--   P2 M Ground Theory Heights  Heights Vertical sec Ideal Of eq map a897c8efb2fb: P2 M Ground Theory Heights  Heights Vertical sec Ideal Of eq map a897c8efb2fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical sec Ideal Of eq map a897c8efb2fb construction uses the P2 M Ground Theory Heights  Heights Vertical sec Ideal Of eq map a897c8efb2fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecMax.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecMax.lean#L14-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecIdealOfPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
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
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_secIdealOf_eq_map_a897c8efb2fb (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K))
    (W : Ideal (MvPolynomial (Fin n) (𝓞 K))) : secIdealOf e I v W = W.map (toSecB e I v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«secIdealOf_eq_map» := P2M_GroundTheory_Heights__Heights_Vertical_secIdealOf_eq_map_a897c8efb2fb
