-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_subsingleton_loc_6c2981eed93b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_subsingleton_loc_6c2981eed93b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:08.134347+00:00
-- url     : https://prove2.me/theorems/d3e127ac-3b0e-59dc-82f0-aadd68ab69a7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin subsingleton loc 6c2981eed93b: P2 M Ground Theory Heights  Heights Kleiman Twist Fin subsingleton loc 6c2981eed93b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin subsingleton loc 6c2981eed93b construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin subsingleton loc 6c2981eed93b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/IsUnitPhiOfMemMonos.lean#L120-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/IsUnitPhiOfMemMonos.lean#L120-L139

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_Graded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
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
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]
variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_subsingleton_loc_6c2981eed93b {I : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ I) (hx : x i = 0) :
    Subsingleton (LocMod (Sy S r) N (TMod x η S n0 d0 g0) I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«subsingleton_loc» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_subsingleton_loc_6c2981eed93b
