-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Published_BernsteinUnitaryProductIrreducible_prod__detRep_462f64e927a8
-- name    : P2M_GlobalTheory_Published_BernsteinUnitaryProductIrreducible_prod__detRep_462f64e927a8
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:54.520116+00:00
-- url     : https://prove2.me/theorems/0b54b7d0-97d1-4b57-815f-10845aaed606
-- title:
--   P2 M Global Theory Published Bernstein Unitary Product Irreducible prod  det Rep 462f64e927a8: P2 M Global Theory Published Bernstein Unitary Product Irreducible prod  det Rep 462f64e927a8
-- statement:
--   The P2 M Global Theory Published Bernstein Unitary Product Irreducible prod  det Rep 462f64e927a8 construction uses the P2 M Global Theory Published Bernstein Unitary Product Irreducible prod  det Rep 462f64e927a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/BernsteinUnitaryProductIrreducible.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/BernsteinUnitaryProductIrreducible.lean#L37-L42

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

theorem P2M_GlobalTheory_Published_BernsteinUnitaryProductIrreducible_prod__detRep_462f64e927a8 (H : BernsteinUnitaryProductIrreducible) {r : ℕ} (t : ℕ)
    {π : Representation ℂ (GL (Fin r) k) V} (s : IsSmooth π) (i : π.IsIrreducible)
    (u : IsUnitarisable π) {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    (prod₂ π (detRep (Fin t) χ)).IsIrreducible := by sorry

alias «GlobalTheory».«Published».«BernsteinUnitaryProductIrreducible».«prod₂_detRep» := P2M_GlobalTheory_Published_BernsteinUnitaryProductIrreducible_prod__detRep_462f64e927a8
