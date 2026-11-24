-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_locPart_normal_f08e45df3bf5
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_locPart_normal_f08e45df3bf5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:55.391335+00:00
-- url     : https://prove2.me/theorems/e3f6fcc5-92b7-45e1-bb6c-5dd6a566632e
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep loc Part normal f08e45df3bf5: P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep loc Part normal f08e45df3bf5
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep loc Part normal f08e45df3bf5 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep loc Part normal f08e45df3bf5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGenSESStep.lean#L63-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGenSESStep.lean#L63-L87

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_locPart_normal_f08e45df3bf5 (h𝓜 : KH.IsMGraded S ι 𝓜) {T : Submonoid (MRingOver S ι)} {c : K → ℤ}
    {x : LocalizedModule T M} (hx : x ∈ KH.locPart ι 𝓜 T c) :
    ∃ (m : M) (t : T) (a : K → ℕ), IsMultiHomog (t : MRingOver S ι) a ∧
      m ∈ 𝓜 (c + fun k => (a k : ℤ)) ∧ x = LocalizedModule.mk m t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GenSESStep».«locPart_normal» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_locPart_normal_f08e45df3bf5
