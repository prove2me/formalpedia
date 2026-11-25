-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_mul_mem_chart_0ccedebfb8fa
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_mul_mem_chart_0ccedebfb8fa
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:01:32.091661+00:00
-- url     : https://prove2.me/theorems/bb058446-c6dc-4e5e-90f8-3b3cd89555d0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman algebra Map mul mem chart 0ccedebfb8fa: P2 M Ground Theory Heights  Heights Kleiman algebra Map mul mem chart 0ccedebfb8fa
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman algebra Map mul mem chart 0ccedebfb8fa construction uses the P2 M Ground Theory Heights  Heights Kleiman algebra Map mul mem chart 0ccedebfb8fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreRestrKer.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreRestrKer.lean#L26-L29

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_mul_mem_chart_0ccedebfb8fa {I : Chart x} (M : Submodule (chartRing S x I) Ω) (d : S) {v : Ω}
    (hv : v ∈ M) : algebraMap S Ω d * v ∈ M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«algebraMap_mul_mem_chart» := P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_mul_mem_chart_0ccedebfb8fa
