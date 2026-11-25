-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redSys_twistSys_zero_4c3119d833e6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_redSys_twistSys_zero_4c3119d833e6
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:03:21.936043+00:00
-- url     : https://prove2.me/theorems/d95a3963-6fa7-427e-b49b-ca7050490a20
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman red Sys twist Sys zero 4c3119d833e6: P2 M Ground Theory Heights  Heights Kleiman red Sys twist Sys zero 4c3119d833e6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman red Sys twist Sys zero 4c3119d833e6 construction uses the P2 M Ground Theory Heights  Heights Kleiman red Sys twist Sys zero 4c3119d833e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionSystems.lean#L104-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionSystems.lean#L104-L116

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_redSys_twistSys_zero_4c3119d833e6 : redSys hxy (twistSys k x 0) 1 = twistSys k y 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«redSys_twistSys_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_redSys_twistSys_zero_4c3119d833e6
