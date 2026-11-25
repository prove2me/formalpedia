-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_mem_range_readChartH0_438c683baf00
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_mem_range_readChartH0_438c683baf00
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:23.545347+00:00
-- url     : https://prove2.me/theorems/6599fa75-2268-44be-a045-03478409ab91
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin mem range read Chart H0 438c683baf00: P2 M Ground Theory Heights  Heights Kleiman Twist Fin mem range read Chart H0 438c683baf00
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin mem range read Chart H0 438c683baf00 construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin mem range read Chart H0 438c683baf00 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/IsUnitPhiOfMemMonos.lean#L171-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/IsUnitPhiOfMemMonos.lean#L171-L202

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_mem_range_readChartH0_438c683baf00 (i0 : Fin (N + 1)) (hi0 : x i0 ≠ 0) (t : Amb x η)
    (ht : ∀ (I : StdCell N) (hI : ∀ i ∈ I.1, x i ≠ 0), ∃ z ∈ degLoc (tgraded x η S n0 d0 g0) 0 I,
      locL x η S n0 d0 g0 I.1 hI z = t) :
    t ∈ LinearMap.range (readChartH0 x η S n0 d0 g0 i0 hi0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«mem_range_readChartH0» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_mem_range_readChartH0_438c683baf00
