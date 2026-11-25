-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_pair_of_dvd_1dbdfd65ac66
-- name    : P2M_GroundTheory_Heights__Heights_AntisymDivisible_pair_of_dvd_1dbdfd65ac66
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:27.347857+00:00
-- url     : https://prove2.me/theorems/a3fdcad3-b210-482e-81e4-a36dfe952945
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Divisible pair of dvd 1dbdfd65ac66: P2 M Ground Theory Heights  Heights Antisym Divisible pair of dvd 1dbdfd65ac66
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Divisible pair of dvd 1dbdfd65ac66 construction uses the P2 M Ground Theory Heights  Heights Antisym Divisible pair of dvd 1dbdfd65ac66 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L73-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L73-L85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {σ : Type*} [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_AntisymDivisible_pair_of_dvd_1dbdfd65ac66 {u v u' v' : σ} (h' : u' ≠ v')
    (hd : (X u - X v : MvPolynomial σ ℝ) ∣ X u' - X v') :
    (u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymDivisible».«pair_of_dvd» := P2M_GroundTheory_Heights__Heights_AntisymDivisible_pair_of_dvd_1dbdfd65ac66
