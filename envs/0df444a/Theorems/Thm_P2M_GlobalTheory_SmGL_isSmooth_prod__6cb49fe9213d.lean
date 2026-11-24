-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SmGL_isSmooth_prod__6cb49fe9213d
-- name    : P2M_GlobalTheory_SmGL_isSmooth_prod__6cb49fe9213d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:34.674751+00:00
-- url     : https://prove2.me/theorems/8b15088a-ac2c-4997-96da-e0acd6e1e694
-- title:
--   P2 M Global Theory Sm GL is Smooth prod  6cb49fe9213d: P2 M Global Theory Sm GL is Smooth prod  6cb49fe9213d
-- statement:
--   The P2 M Global Theory Sm GL is Smooth prod  6cb49fe9213d construction uses the P2 M Global Theory Sm GL is Smooth prod  6cb49fe9213d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean#L370-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean#L370-L371

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {k}
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem P2M_GlobalTheory_SmGL_isSmooth_prod__6cb49fe9213d {r t : ℕ} (π₁ : Representation ℂ (GL (Fin r) k) V)
    (π₂ : Representation ℂ (GL (Fin t) k) W) : IsSmooth (prod₂ π₁ π₂) := by sorry

alias «GlobalTheory».«SmGL».«isSmooth_prod₂» := P2M_GlobalTheory_SmGL_isSmooth_prod__6cb49fe9213d
