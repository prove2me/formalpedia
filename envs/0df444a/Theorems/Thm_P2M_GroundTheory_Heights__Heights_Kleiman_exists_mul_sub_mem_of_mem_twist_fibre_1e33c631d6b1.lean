-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_sub_mem_of_mem_twist_fibre_1e33c631d6b1
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_sub_mem_of_mem_twist_fibre_1e33c631d6b1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:33.163439+00:00
-- url     : https://prove2.me/theorems/7ea83506-d33d-4713-8348-94c40c677999
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists mul sub mem of mem twist fibre 1e33c631d6b1: P2 M Ground Theory Heights  Heights Kleiman exists mul sub mem of mem twist fibre 1e33c631d6b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists mul sub mem of mem twist fibre 1e33c631d6b1 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists mul sub mem of mem twist fibre 1e33c631d6b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreRestrKer.lean#L73-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreRestrKer.lean#L73-L146

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreRestrKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreRestrKer
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
open MvPolynomial Filter
open scoped Pointwise nonZeroDivisors
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_sub_mem_of_mem_twist_fibre_1e33c631d6b1 {F : Type u} [Field F] [Algebra S F] [Algebra F Ω]
    [IsScalarTower S F Ω] (Q : SubSystem S x Ω) {qq : Ideal (Poly S N)}
    (hhom : ∀ p ∈ qq, ∀ d : ℕ, homogeneousComponent d p ∈ qq) (𝔪 : Ideal S) {b : F}
    (hb : ∀ a ∈ 𝔪, ∃ d : S, b * algebraMap S F a = algebraMap S F d) (I : Chart x) {t : Ω}
    (ht : t ∈ (Q.twist (idealSys x (qq ⊔ 𝔪.map (C : S →+* Poly S N)))).sub I) :
    ∃ u ∈ (Q.twist (idealSys x qq)).sub I, algebraMap F Ω b * (t - u) ∈ Q.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_mul_sub_mem_of_mem_twist_fibre» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_sub_mem_of_mem_twist_fibre_1e33c631d6b1
