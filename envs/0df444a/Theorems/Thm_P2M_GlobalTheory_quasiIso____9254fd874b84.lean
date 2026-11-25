-- Prove2me | Theorems.Thm_P2M_GlobalTheory_quasiIso____9254fd874b84
-- name    : P2M_GlobalTheory_quasiIso____9254fd874b84
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:43.888922+00:00
-- url     : https://prove2.me/theorems/41915b13-f9fd-46ea-a922-5c8ece0c22d8
-- title:
--   P2 M Global Theory quasi Iso    9254fd874b84: P2 M Global Theory quasi Iso    9254fd874b84
-- statement:
--   The P2 M Global Theory quasi Iso    9254fd874b84 construction uses the P2 M Global Theory quasi Iso    9254fd874b84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L682-L688
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L682-L688

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

theorem P2M_GlobalTheory_quasiIso____9254fd874b84 (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by sorry

alias «GlobalTheory».«quasiIso_τ₂» := P2M_GlobalTheory_quasiIso____9254fd874b84
