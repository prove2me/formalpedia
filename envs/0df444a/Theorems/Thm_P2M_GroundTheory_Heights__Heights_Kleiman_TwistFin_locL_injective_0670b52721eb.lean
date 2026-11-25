-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_injective_0670b52721eb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_injective_0670b52721eb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:01:06.109446+00:00
-- url     : https://prove2.me/theorems/b6367151-112e-53e8-9692-cefdb5be1e94
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin loc L injective 0670b52721eb: P2 M Ground Theory Heights  Heights Kleiman Twist Fin loc L injective 0670b52721eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin loc L injective 0670b52721eb construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin loc L injective 0670b52721eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/IsUnitPhiOfMemMonos.lean#L90-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/IsUnitPhiOfMemMonos.lean#L90-L108

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_injective_0670b52721eb (I : Finset (Fin (N + 1))) (hI : ∀ i ∈ I, x i ≠ 0) :
    Function.Injective (locL x η S n0 d0 g0 I hI) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«locL_injective» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_injective_0670b52721eb
