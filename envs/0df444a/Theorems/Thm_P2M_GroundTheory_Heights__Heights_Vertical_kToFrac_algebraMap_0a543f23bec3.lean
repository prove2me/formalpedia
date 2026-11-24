-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_kToFrac_algebraMap_0a543f23bec3
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_kToFrac_algebraMap_0a543f23bec3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:38.475221+00:00
-- url     : https://prove2.me/theorems/12dce8ed-3c38-4b84-8b15-33f02b18f0f7
-- title:
--   P2 M Ground Theory Heights  Heights Vertical k To Frac algebra Map 0a543f23bec3: P2 M Ground Theory Heights  Heights Vertical k To Frac algebra Map 0a543f23bec3
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical k To Frac algebra Map 0a543f23bec3 construction uses the P2 M Ground Theory Heights  Heights Vertical k To Frac algebra Map 0a543f23bec3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean#L28-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormIdentity
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
variable {K : Type*} [Field K] [NumberField K] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_kToFrac_algebraMap_0a543f23bec3 (e n : ℕ) (a : 𝓞 K) :
    kToFrac K e n (algebraMap (𝓞 K) K a) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (C a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«kToFrac_algebraMap» := P2M_GroundTheory_Heights__Heights_Vertical_kToFrac_algebraMap_0a543f23bec3
