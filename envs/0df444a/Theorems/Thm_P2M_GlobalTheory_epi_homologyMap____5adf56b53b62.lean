-- Prove2me | Theorems.Thm_P2M_GlobalTheory_epi_homologyMap____5adf56b53b62
-- name    : P2M_GlobalTheory_epi_homologyMap____5adf56b53b62
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:11:52.512799+00:00
-- url     : https://prove2.me/theorems/6e3120bd-9f04-4263-b593-ec040e855eb2
-- title:
--   P2 M Global Theory epi homology Map    5adf56b53b62: P2 M Global Theory epi homology Map    5adf56b53b62
-- statement:
--   The P2 M Global Theory epi homology Map    5adf56b53b62 construction uses the P2 M Global Theory epi homology Map    5adf56b53b62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L664-L680
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L664-L680

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

theorem P2M_GlobalTheory_epi_homologyMap____5adf56b53b62 (i : ι) (h₁ : Epi (homologyMap φ.τ₁ i))
    (h₂ : Epi (homologyMap φ.τ₃ i)) (h₃ : ∀ j, c.Rel i j → Mono (homologyMap φ.τ₁ j)) :
    Epi (homologyMap φ.τ₂ i) := by sorry

alias «GlobalTheory».«epi_homologyMap_τ₂» := P2M_GlobalTheory_epi_homologyMap____5adf56b53b62
