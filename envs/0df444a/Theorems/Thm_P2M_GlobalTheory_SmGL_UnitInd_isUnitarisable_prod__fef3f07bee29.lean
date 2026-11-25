-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SmGL_UnitInd_isUnitarisable_prod__fef3f07bee29
-- name    : P2M_GlobalTheory_SmGL_UnitInd_isUnitarisable_prod__fef3f07bee29
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:55.450527+00:00
-- url     : https://prove2.me/theorems/7f20b43e-bb2a-469b-a4f2-6411c66e6df3
-- title:
--   P2 M Global Theory Sm GL Unit Ind is Unitarisable prod  fef3f07bee29: P2 M Global Theory Sm GL Unit Ind is Unitarisable prod  fef3f07bee29
-- statement:
--   The P2 M Global Theory Sm GL Unit Ind is Unitarisable prod  fef3f07bee29 construction uses the P2 M Global Theory Sm GL Unit Ind is Unitarisable prod  fef3f07bee29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantModulus.lean#L482-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantModulus.lean#L482-L485

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
open GlobalTheory.SplitFlip
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem P2M_GlobalTheory_SmGL_UnitInd_isUnitarisable_prod__fef3f07bee29 {r t : ℕ} {π₁ : Representation ℂ (GL (Fin r) k) V}
    {π₂ : Representation ℂ (GL (Fin t) k) W} (h₁ : IsUnitarisable π₁) (h₂ : IsUnitarisable π₂) :
    IsUnitarisable (prod₂ π₁ π₂) := by sorry

alias «GlobalTheory».«SmGL».«UnitInd».«isUnitarisable_prod₂» := P2M_GlobalTheory_SmGL_UnitInd_isUnitarisable_prod__fef3f07bee29
