-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Published_BernsteinUnitaryProductIrreducible_ind__stdSum_ee64510dd378
-- name    : P2M_GlobalTheory_Published_BernsteinUnitaryProductIrreducible_ind__stdSum_ee64510dd378
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:05.515526+00:00
-- url     : https://prove2.me/theorems/82eeace5-2b19-44aa-bff6-338298c2482b
-- title:
--   P2 M Global Theory Published Bernstein Unitary Product Irreducible ind  std Sum ee64510dd378: P2 M Global Theory Published Bernstein Unitary Product Irreducible ind  std Sum ee64510dd378
-- statement:
--   The P2 M Global Theory Published Bernstein Unitary Product Irreducible ind  std Sum ee64510dd378 construction uses the P2 M Global Theory Published Bernstein Unitary Product Irreducible ind  std Sum ee64510dd378 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/BernsteinUnitaryProductIrreducible.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/BernsteinUnitaryProductIrreducible.lean#L23-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.BernsteinUnitaryProductIrreducible
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem P2M_GlobalTheory_Published_BernsteinUnitaryProductIrreducible_ind__stdSum_ee64510dd378 (H : BernsteinUnitaryProductIrreducible) {r t N : ℕ} (h : r + t = N)
    {π₁ : Representation ℂ (GL (Fin r) k) V} {π₂ : Representation ℂ (GL (Fin t) k) W}
    (s₁ : IsSmooth π₁) (i₁ : π₁.IsIrreducible) (u₁ : IsUnitarisable π₁)
    (s₂ : IsSmooth π₂) (i₂ : π₂.IsIrreducible) (u₂ : IsUnitarisable π₂) :
    (ind₂ (stdSum h) (extTensor π₁ π₂)).IsIrreducible := by sorry

alias «GlobalTheory».«Published».«BernsteinUnitaryProductIrreducible».«ind₂_stdSum» := P2M_GlobalTheory_Published_BernsteinUnitaryProductIrreducible_ind__stdSum_ee64510dd378
