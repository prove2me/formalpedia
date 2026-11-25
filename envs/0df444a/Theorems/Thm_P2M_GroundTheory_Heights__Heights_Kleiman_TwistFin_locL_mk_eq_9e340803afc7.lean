-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_mk_eq_9e340803afc7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_mk_eq_9e340803afc7
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:16:40.82781+00:00
-- url     : https://prove2.me/theorems/504f497d-a7ea-490b-b31a-1a8b96d4e818
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin loc L mk eq 9e340803afc7: P2 M Ground Theory Heights  Heights Kleiman Twist Fin loc L mk eq 9e340803afc7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin loc L mk eq 9e340803afc7 construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin loc L mk eq 9e340803afc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/IsUnitPhiOfMemMonos.lean#L80-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/IsUnitPhiOfMemMonos.lean#L80-L88

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_mk_eq_9e340803afc7 (I : Finset (Fin (N + 1))) (hI : ∀ i ∈ I, x i ≠ 0) (m : TMod x η S n0 d0 g0)
    (s : monos (S := Sy S r) I) (a : Amb x η) (ha : phi x η S s * toA x η a = toA x η m) :
    locL x η S n0 d0 g0 I hI
      (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0)) = a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«locL_mk_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_mk_eq_9e340803afc7
