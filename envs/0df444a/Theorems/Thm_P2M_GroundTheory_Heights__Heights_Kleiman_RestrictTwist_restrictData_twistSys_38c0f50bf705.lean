-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_restrictData_twistSys_38c0f50bf705
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_restrictData_twistSys_38c0f50bf705
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:09:57.521819+00:00
-- url     : https://prove2.me/theorems/050cbfaf-cb79-50d5-99c7-1f2a8d29bf2c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist restrict Data twist Sys 38c0f50bf705: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist restrict Data twist Sys 38c0f50bf705
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist restrict Data twist Sys 38c0f50bf705 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist restrict Data twist Sys 38c0f50bf705 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L124-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L124-L148

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_restrictData_twistSys_38c0f50bf705 {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
    (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (c : ℤ) :
    RestrictData (twistSys S x c) hxy (twistSys S y c) (twistRes S x y c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«restrictData_twistSys» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_restrictData_twistSys_38c0f50bf705
