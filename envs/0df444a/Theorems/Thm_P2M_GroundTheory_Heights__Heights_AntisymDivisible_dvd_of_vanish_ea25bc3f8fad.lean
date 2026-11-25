-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_dvd_of_vanish_ea25bc3f8fad
-- name    : P2M_GroundTheory_Heights__Heights_AntisymDivisible_dvd_of_vanish_ea25bc3f8fad
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:52.785342+00:00
-- url     : https://prove2.me/theorems/edff7165-5e63-40f2-bfe8-192cfb7ff4de
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Divisible dvd of vanish ea25bc3f8fad: P2 M Ground Theory Heights  Heights Antisym Divisible dvd of vanish ea25bc3f8fad
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Divisible dvd of vanish ea25bc3f8fad construction uses the P2 M Ground Theory Heights  Heights Antisym Divisible dvd of vanish ea25bc3f8fad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L41-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L41-L52

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

theorem P2M_GroundTheory_Heights__Heights_AntisymDivisible_dvd_of_vanish_ea25bc3f8fad (u v : σ) (P : MvPolynomial σ ℝ)
    (h : ∀ x : σ → ℝ, x u = x v → eval x P = 0) : (X u - X v) ∣ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymDivisible».«dvd_of_vanish» := P2M_GroundTheory_Heights__Heights_AntisymDivisible_dvd_of_vanish_ea25bc3f8fad
