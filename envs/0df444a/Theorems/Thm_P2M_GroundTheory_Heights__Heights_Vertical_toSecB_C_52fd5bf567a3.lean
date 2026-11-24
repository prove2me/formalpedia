-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_toSecB_C_52fd5bf567a3
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_toSecB_C_52fd5bf567a3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:40.330744+00:00
-- url     : https://prove2.me/theorems/71ccae04-9056-4550-9d02-697efbde1f2d
-- title:
--   P2 M Ground Theory Heights  Heights Vertical to Sec B C 52fd5bf567a3: P2 M Ground Theory Heights  Heights Vertical to Sec B C 52fd5bf567a3
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical to Sec B C 52fd5bf567a3 construction uses the P2 M Ground Theory Heights  Heights Vertical to Sec B C 52fd5bf567a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecMax.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecMax.lean#L18-L23

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_toSecB_C_52fd5bf567a3 (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    toSecB e I v (C a) = algebraMap (ParDVR e n v) (SecB e I v)
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C a)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«toSecB_C» := P2M_GroundTheory_Heights__Heights_Vertical_toSecB_C_52fd5bf567a3
