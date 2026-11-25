-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CoeffExt_finrank_fun__0788e41184fe
-- name    : P2M_GlobalTheory_CoeffExt_finrank_fun__0788e41184fe
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:24.831882+00:00
-- url     : https://prove2.me/theorems/99ab7ca6-b747-4834-ac56-c5aa081cf948
-- title:
--   P2 M Global Theory Coeff Ext finrank fun  0788e41184fe: P2 M Global Theory Coeff Ext finrank fun  0788e41184fe
-- statement:
--   The P2 M Global Theory Coeff Ext finrank fun  0788e41184fe construction uses the P2 M Global Theory Coeff Ext finrank fun  0788e41184fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L166-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L166-L177

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffExt
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module LL' V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V']
    {ρ : Representation LL G V} {ρ' : Representation LL' G V'}
    {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[LL] (ι → V)}

theorem P2M_GlobalTheory_CoeffExt_finrank_fun__0788e41184fe {F M : Type} [Field F] [AddCommGroup M] [Module F M] (ι : Type) [Fintype ι] :
    finrank F (ι → M) = Fintype.card ι * finrank F M := by sorry

alias «GlobalTheory».«CoeffExt».«finrank_fun'» := P2M_GlobalTheory_CoeffExt_finrank_fun__0788e41184fe
