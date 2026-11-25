-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_locRes_269addb87c40
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_locRes_269addb87c40
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:01:12.6451+00:00
-- url     : https://prove2.me/theorems/78ce5de1-fb54-53ac-a618-2cd8d6c4b055
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin loc L loc Res 269addb87c40: P2 M Ground Theory Heights  Heights Kleiman Twist Fin loc L loc Res 269addb87c40
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin loc L loc Res 269addb87c40 construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin loc L loc Res 269addb87c40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/IsUnitPhiOfMemMonos.lean#L110-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/IsUnitPhiOfMemMonos.lean#L110-L118

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_locRes_269addb87c40 {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (hJ : ∀ i ∈ J, x i ≠ 0)
    (z : LocMod (Sy S r) N (TMod x η S n0 d0 g0) I) :
    locL x η S n0 d0 g0 J hJ (locRes h z) = locL x η S n0 d0 g0 I (fun i hi => hJ i (h hi)) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«locL_locRes» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_locRes_269addb87c40
