-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redSys_pow_6339957ad07c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_redSys_pow_6339957ad07c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:38:23.64121+00:00
-- url     : https://prove2.me/theorems/b3e905be-3f9d-492c-9c66-4f98f3da749c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman red Sys pow 6339957ad07c: P2 M Ground Theory Heights  Heights Kleiman red Sys pow 6339957ad07c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman red Sys pow 6339957ad07c construction uses the P2 M Ground Theory Heights  Heights Kleiman red Sys pow 6339957ad07c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionSystems.lean#L118-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionSystems.lean#L118-L128

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp

theorem P2M_GroundTheory_Heights__Heights_Kleiman_redSys_pow_6339957ad07c {P : SubSystem k x Ω} {γ : Ω} (hP : RedGood hxy P γ) (n : ℕ) :
    RedGood hxy (P.pow n) (γ ^ n) ∧ redSys hxy (P.pow n) (γ ^ n) = (redSys hxy P γ).pow n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«redSys_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_redSys_pow_6339957ad07c
