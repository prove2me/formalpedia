-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_mk_mem_locPart_8ee0fd2ff896
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_mk_mem_locPart_8ee0fd2ff896
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:16.906271+00:00
-- url     : https://prove2.me/theorems/a22082b1-482a-4173-be44-b03fb25b4027
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep mk mem loc Part 8ee0fd2ff896: P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep mk mem loc Part 8ee0fd2ff896
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep mk mem loc Part 8ee0fd2ff896 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep mk mem loc Part 8ee0fd2ff896 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGenSESStep.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGenSESStep.lean#L58-L61

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_mk_mem_locPart_8ee0fd2ff896 {T : Submonoid (MRingOver S ι)} {c : K → ℤ} (m : M) (t : T) (a : K → ℕ)
    (ht : IsMultiHomog (t : MRingOver S ι) a) (hm : m ∈ 𝓜 (c + fun k => (a k : ℤ))) :
    LocalizedModule.mk m t ∈ KH.locPart ι 𝓜 T c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GenSESStep».«mk_mem_locPart» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_mk_mem_locPart_8ee0fd2ff896
