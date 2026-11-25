-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_monos_mul_mem_twistMod_all_a09b6e3395b8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_monos_mul_mem_twistMod_all_a09b6e3395b8
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:06:05.449653+00:00
-- url     : https://prove2.me/theorems/07f15a35-60ed-5333-aa2d-83a75127586e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists monos mul mem twist Mod all a09b6e3395b8: P2 M Ground Theory Heights  Heights Kleiman exists monos mul mem twist Mod all a09b6e3395b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists monos mul mem twist Mod all a09b6e3395b8 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists monos mul mem twist Mod all a09b6e3395b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutDimLower.lean#L21-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutDimLower.lean#L21-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutDimLowerSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutDimLower
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_monos_mul_mem_twistMod_all_a09b6e3395b8 (L : LineBundle S x) (I : Chart x) (y : Ω)
    (hy : ∀ δ ∈ L.sub I, y * δ ∈ chartRing S x I) :
    ∃ U ∈ monos (S := S) I.1, ∃ dU : ℕ, U.IsHomogeneous dU ∧
      ∀ (K : Chart x), ∀ δ ∈ L.sub K, aeval x U * (y * δ) ∈ twistMod S x (dU : ℤ) K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_monos_mul_mem_twistMod_all» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_monos_mul_mem_twistMod_all_a09b6e3395b8
