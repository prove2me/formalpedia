-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SmGL_jac__detRep_55f87710e6d0
-- name    : P2M_GlobalTheory_SmGL_jac__detRep_55f87710e6d0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:39.983797+00:00
-- url     : https://prove2.me/theorems/ceeee2e4-1b70-5f1d-9f3c-df08985b31f9
-- title:
--   P2 M Global Theory Sm GL jac  det Rep 55f87710e6d0: P2 M Global Theory Sm GL jac  det Rep 55f87710e6d0
-- statement:
--   The P2 M Global Theory Sm GL jac  det Rep 55f87710e6d0 construction uses the P2 M Global Theory Sm GL jac  det Rep 55f87710e6d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean#L373-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean#L373-L391

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

theorem P2M_GlobalTheory_SmGL_jac__detRep_55f87710e6d0 (e : a ⊕ b ≃ n) (χ : kˣ →* ℂˣ) (g : GL a k × GL b k)
    (x : Jacquet (detRep n χ) (unipRad k (two e))) :
    jac₂ e (detRep n χ) g x =
      ((detChar a (χ * absPow k (-(Fintype.card b : ℂ) / 2)) g.1 *
        detChar b (χ * absPow k ((Fintype.card a : ℂ) / 2)) g.2 : ℂˣ) : ℂ) • x := by sorry

alias «GlobalTheory».«SmGL».«jac₂_detRep» := P2M_GlobalTheory_SmGL_jac__detRep_55f87710e6d0
