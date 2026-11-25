-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_upward_594d791661c9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KThm_upward_594d791661c9
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:00:15.930049+00:00
-- url     : https://prove2.me/theorems/cf49c46d-5e3c-4678-aae0-f4b6940c2076
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KThm upward 594d791661c9: P2 M Ground Theory Heights  Heights Kleiman KThm upward 594d791661c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KThm upward 594d791661c9 construction uses the P2 M Ground Theory Heights  Heights Kleiman KThm upward 594d791661c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L198-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L198-L237

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KThm_upward_594d791661c9 (hJ : GraphClosed.Statement.{u, w}) (M : LineBundle k x) (P : ℕ) (m' : ℤ)
    (hP : 1 ≤ P) (hG : (twistMul M.toSubSystem P m').Generated) (t : ℚ) (ht : (m' : ℚ) < P * t) :
    ∃ (p : ℕ) (m : ℤ), 1 ≤ p ∧ (m : ℚ) = p * t ∧ IsVeryAmple (twistMul M.toSubSystem p m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KThm».«upward» := P2M_GroundTheory_Heights__Heights_Kleiman_KThm_upward_594d791661c9
