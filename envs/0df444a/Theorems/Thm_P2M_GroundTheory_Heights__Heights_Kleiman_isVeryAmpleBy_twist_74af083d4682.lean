-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmpleBy_twist_74af083d4682
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmpleBy_twist_74af083d4682
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:01:17.817435+00:00
-- url     : https://prove2.me/theorems/b57206ee-e646-48ba-949e-7370121f8a4d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman is Very Ample By twist 74af083d4682: P2 M Ground Theory Heights  Heights Kleiman is Very Ample By twist 74af083d4682
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman is Very Ample By twist 74af083d4682 construction uses the P2 M Ground Theory Heights  Heights Kleiman is Very Ample By twist 74af083d4682 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L229-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L229-L269

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleTwistGenerated
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
open scoped Pointwise
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable {L G : SubSystem k x Ω} {r₁ s₁ : ℕ} {h : Fin (r₁ + 1) → Ω} {g : Fin (s₁ + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmpleBy_twist_74af083d4682 {R : ℕ} (hL : IsVeryAmpleBy L h) (hgs : ∀ j, g j ∈ G.secs)
    (hgg : ∀ I, Submodule.span (chartRing k x I) (Set.range g) = G.sub I)
    (e : Fin (R + 1) ≃ Fin (r₁ + 1) × Fin (s₁ + 1)) :
    IsVeryAmpleBy (L.twist G) (fun p => h (e p).1 * g (e p).2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«isVeryAmpleBy_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmpleBy_twist_74af083d4682
