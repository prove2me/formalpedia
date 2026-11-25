-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_idealMod_of_algebraMap_mul_mem_d6a9246660b6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_idealMod_of_algebraMap_mul_mem_d6a9246660b6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:14:03.120512+00:00
-- url     : https://prove2.me/theorems/248f1ad0-5401-45a2-834e-39cb03811389
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem ideal Mod of algebra Map mul mem d6a9246660b6: P2 M Ground Theory Heights  Heights Kleiman mem ideal Mod of algebra Map mul mem d6a9246660b6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem ideal Mod of algebra Map mul mem d6a9246660b6 construction uses the P2 M Ground Theory Heights  Heights Kleiman mem ideal Mod of algebra Map mul mem d6a9246660b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrQuotTorsionFree.lean#L41-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrQuotTorsionFree.lean#L41-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrQuotTorsionFree
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_idealMod_of_algebraMap_mul_mem_d6a9246660b6 {qq : Ideal (Poly S N)} (hq : qq.IsPrime)
    (hle : ∀ (p : Poly S N) (d : ℕ), p.IsHomogeneous d → aeval x p = 0 → p ∈ qq) (I : Chart x) {s : S}
    (hs : (C s : Poly S N) ∉ qq) {a : Ω} (ha : a ∈ chartRing S x I)
    (hsa : algebraMap S Ω s * a ∈ idealMod qq I) : a ∈ idealMod qq I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_idealMod_of_algebraMap_mul_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_idealMod_of_algebraMap_mul_mem_d6a9246660b6
