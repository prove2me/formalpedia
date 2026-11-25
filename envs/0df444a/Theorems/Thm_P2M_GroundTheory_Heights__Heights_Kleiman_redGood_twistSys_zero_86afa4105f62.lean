-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redGood_twistSys_zero_86afa4105f62
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_redGood_twistSys_zero_86afa4105f62
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:03:44.289738+00:00
-- url     : https://prove2.me/theorems/baaf1303-5062-4d1b-a9e9-874c9f8e06dd
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman red Good twist Sys zero 86afa4105f62: P2 M Ground Theory Heights  Heights Kleiman red Good twist Sys zero 86afa4105f62
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman red Good twist Sys zero 86afa4105f62 construction uses the P2 M Ground Theory Heights  Heights Kleiman red Good twist Sys zero 86afa4105f62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionSystems.lean#L100-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionSystems.lean#L100-L102

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_redGood_twistSys_zero_86afa4105f62 : RedGood hxy (twistSys k x 0) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«redGood_twistSys_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_redGood_twistSys_zero_86afa4105f62
