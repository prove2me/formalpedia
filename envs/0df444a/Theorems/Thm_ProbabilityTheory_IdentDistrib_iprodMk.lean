-- Prove2me | Theorems.Thm_ProbabilityTheory_IdentDistrib_iprodMk
-- name    : ProbabilityTheory.IdentDistrib.iprodMk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:28:40.332496+00:00
-- url     : https://prove2.me/theorems/e53c9ec4-aa35-4604-aa79-ef0c53d58af0
-- title:
--   Ident Distrib: iprod Mk
-- statement:
--   The Ident Distrib construction uses the iprod Mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L193-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L193-L212

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Measure Filter Set
open scoped Topology MeasureTheory ENNReal NNReal
attribute [symm] ProbabilityTheory.IdentDistrib.symm
variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]
open MeasureTheory ProbabilityTheory Function Set
open ProbabilityTheory
universe u u' v
variable {Ω Ω' α ι β β' T : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mβ : MeasurableSpace β} {μ : Measure Ω} {ν : Measure Ω'} {f g : Ω
    → β} {f' g' : Ω' → β}

theorem ProbabilityTheory.IdentDistrib.iprodMk
    {I : Type*} [Finite I] {F : I → Ω → β} {F' : I → Ω' → β}
    (hFF' : ∀ i, IdentDistrib (F i) (F' i) μ ν) (hμ : IsProbabilityMeasure μ)
    (hν : IsProbabilityMeasure ν) (h : iIndepFun F μ) (h' : iIndepFun F' ν) :
    IdentDistrib (fun x i ↦ F i x) (fun x i ↦ F' i x) μ ν := by sorry
