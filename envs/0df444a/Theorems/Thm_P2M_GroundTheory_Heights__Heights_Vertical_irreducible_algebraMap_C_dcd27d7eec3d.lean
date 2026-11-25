-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_irreducible_algebraMap_C_dcd27d7eec3d
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_irreducible_algebraMap_C_dcd27d7eec3d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:43:35.203956+00:00
-- url     : https://prove2.me/theorems/cdebfdf5-744a-4be2-b9cb-d08e7130b01c
-- title:
--   P2 M Ground Theory Heights  Heights Vertical irreducible algebra Map C dcd27d7eec3d: P2 M Ground Theory Heights  Heights Vertical irreducible algebra Map C dcd27d7eec3d
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical irreducible algebra Map C dcd27d7eec3d construction uses the P2 M Ground Theory Heights  Heights Vertical irreducible algebra Map C dcd27d7eec3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGaussDVR.lean#L72-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGaussDVR.lean#L72-L110

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_irreducible_algebraMap_C_dcd27d7eec3d (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    [IsDiscreteValuationRing (ParDVR e n v)] {a : 𝓞 K} (ha : v.intValuation a = exp (-1 : ℤ)) :
    Irreducible (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C a)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«irreducible_algebraMap_C» := P2M_GroundTheory_Heights__Heights_Vertical_irreducible_algebraMap_C_dcd27d7eec3d
