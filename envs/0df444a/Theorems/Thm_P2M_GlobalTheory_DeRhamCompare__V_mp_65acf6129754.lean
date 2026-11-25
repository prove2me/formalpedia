-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DeRhamCompare__V_mp_65acf6129754
-- name    : P2M_GlobalTheory_DeRhamCompare__V_mp_65acf6129754
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:05:28.754082+00:00
-- url     : https://prove2.me/theorems/94993aaf-73a7-52e5-8c0d-079284c35d8c
-- title:
--   P2 M Global Theory De Rham Compare  V mp 65acf6129754: P2 M Global Theory De Rham Compare  V mp 65acf6129754
-- statement:
--   The P2 M Global Theory De Rham Compare  V mp 65acf6129754 construction uses the P2 M Global Theory De Rham Compare  V mp 65acf6129754 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ActQdRPeriodTEqCyclotomicBottom.lean#L283-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ActQdRPeriodTEqCyclotomicBottom.lean#L283-L289

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_DualExactSequence
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_JumpMultiplicityDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ActQdRPeriodTEqCyclotomicBottom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DeRhamCompare
open Module
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod tdR filDdR jumpMult)
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem P2M_GlobalTheory_DeRhamCompare__V_mp_65acf6129754 (c : B) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulPeriod (Qp := Qp) (LL := LL) (V := V) c x) =
      mulPeriod (Qp := Qp) (LL := LL) (V := V) (PD.ι c) (ιV PD (LL := LL) (V := V) x) := by sorry

alias «GlobalTheory».«DeRhamCompare».«ιV_mp» := P2M_GlobalTheory_DeRhamCompare__V_mp_65acf6129754
