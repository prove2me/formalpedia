-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_twist_idealSys_of_algebraMap_mul_mem_7c334198a913
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_twist_idealSys_of_algebraMap_mul_mem_7c334198a913
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:02:23.050432+00:00
-- url     : https://prove2.me/theorems/1bfe3714-b3bf-494f-9a5a-69737554b6fe
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem twist ideal Sys of algebra Map mul mem 7c334198a913: P2 M Ground Theory Heights  Heights Kleiman mem twist ideal Sys of algebra Map mul mem 7c334198a913
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem twist ideal Sys of algebra Map mul mem 7c334198a913 construction uses the P2 M Ground Theory Heights  Heights Kleiman mem twist ideal Sys of algebra Map mul mem 7c334198a913 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreRestrKer.lean#L37-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreRestrKer.lean#L37-L71

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_twist_idealSys_of_algebraMap_mul_mem_7c334198a913 {qq : Ideal (Poly S N)} [hq : qq.IsPrime]
    (hle : primeOf (S := S) x ≤ qq) (hconst : ∀ s : S, (C s : Poly S N) ∈ qq → s = 0)
    (Q : LineBundle S x) (I : Chart x) {s₀ : S} (hs₀ : s₀ ≠ 0) {v : Ω} (hv : v ∈ Q.sub I)
    (hsv : algebraMap S Ω s₀ * v ∈ (Q.twist (idealSys x qq)).sub I) :
    v ∈ (Q.twist (idealSys x qq)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_twist_idealSys_of_algebraMap_mul_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_twist_idealSys_of_algebraMap_mul_mem_7c334198a913
