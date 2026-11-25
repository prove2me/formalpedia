-- Prove2me | Theorems.Thm_P2M_GlobalTheory_mono_homologyMap____340fdbb5f679
-- name    : P2M_GlobalTheory_mono_homologyMap____340fdbb5f679
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:35.746582+00:00
-- url     : https://prove2.me/theorems/7c1def22-379f-49cc-93eb-7700d4208208
-- title:
--   P2 M Global Theory mono homology Map    340fdbb5f679: P2 M Global Theory mono homology Map    340fdbb5f679
-- statement:
--   The P2 M Global Theory mono homology Map    340fdbb5f679 construction uses the P2 M Global Theory mono homology Map    340fdbb5f679 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L646-L662
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L646-L662

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
open ComposableArrows Abelian HomologySequence
variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
include hS₁ hS₂

theorem P2M_GlobalTheory_mono_homologyMap____340fdbb5f679 (j : ι) (h₁ : Mono (homologyMap φ.τ₁ j))
    (h₂ : Mono (homologyMap φ.τ₃ j)) (h₃ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₃ i)) :
    Mono (homologyMap φ.τ₂ j) := by sorry

alias «GlobalTheory».«mono_homologyMap_τ₂» := P2M_GlobalTheory_mono_homologyMap____340fdbb5f679
