-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DRFil__V_mem_DdR_4a0c80958f6e
-- name    : P2M_GlobalTheory_DRFil__V_mem_DdR_4a0c80958f6e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:27.994805+00:00
-- url     : https://prove2.me/theorems/a079d898-0728-46bb-a187-47976c9728f0
-- title:
--   P2 M Global Theory DRFil  V mem Dd R 4a0c80958f6e: P2 M Global Theory DRFil  V mem Dd R 4a0c80958f6e
-- statement:
--   The P2 M Global Theory DRFil  V mem Dd R 4a0c80958f6e construction uses the P2 M Global Theory DRFil  V mem Dd R 4a0c80958f6e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComponentEquiv.lean#L106-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComponentEquiv.lean#L106-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComponentEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']

theorem P2M_GlobalTheory_DRFil__V_mem_DdR_4a0c80958f6e (ρ : Representation LL G V) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    ιV PD (LL := LL) (V := V) x ∈ DdR PD ρ := by sorry

alias «GlobalTheory».«DRFil».«ιV_mem_DdR» := P2M_GlobalTheory_DRFil__V_mem_DdR_4a0c80958f6e
