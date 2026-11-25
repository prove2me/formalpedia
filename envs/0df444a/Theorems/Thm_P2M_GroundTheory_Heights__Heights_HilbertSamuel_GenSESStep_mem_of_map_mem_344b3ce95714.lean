-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_mem_of_map_mem_344b3ce95714
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_mem_of_map_mem_344b3ce95714
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:31.503138+00:00
-- url     : https://prove2.me/theorems/3572c1e8-a163-40b6-9f15-25ba169bc3a0
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep mem of map mem 344b3ce95714: P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep mem of map mem 344b3ce95714
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep mem of map mem 344b3ce95714 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep mem of map mem 344b3ce95714 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGenSESStep.lean#L112-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGenSESStep.lean#L112-L145

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGenSESStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
variable {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_mem_of_map_mem_344b3ce95714 {M' : Type*} [AddCommGroup M'] [Module (MRingOver S ι) M'] [Module S M']
    [IsScalarTower S (MRingOver S ι) M'] {𝓜' : (K → ℤ) → Submodule S M'} (h𝓜' : KH.IsMGraded S ι 𝓜')
    (h𝓜 : KH.IsMGraded S ι 𝓜) {g : M' →ₗ[MRingOver S ι] M} (hg : KH.IsMGradedMap S ι 𝓜' 𝓜 g)
    (hinj : Function.Injective g) {c : K → ℤ} {m' : M'} (hm : g m' ∈ 𝓜 c) : m' ∈ 𝓜' c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GenSESStep».«mem_of_map_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_mem_of_map_mem_344b3ce95714
