-- Prove2me | Theorems.Thm_ProbabilityTheory_IdentDistrib_comp_left__6eb147
-- name    : ProbabilityTheory.IdentDistrib.comp_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:26:01.595266+00:00
-- url     : https://prove2.me/theorems/6eb1471f-5885-4401-8d8a-dac80c5153e1
-- title:
--   Ident Distrib: comp left
-- statement:
--   Composing identically distributed functions with a measurable embedding of conull
--   range
--   gives identically distributed functions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L135-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L135-L139

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
open ProbabilityTheory
variable {μ : Measure α} {ν : Measure β} {f f' : α → γ} {g g' : β → γ} {s : Set γ}

theorem ProbabilityTheory.IdentDistrib.comp_left
    {i : δ → α} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂μ,
  a ∈ range i)
    (hf : Measurable f) (hfg : IdentDistrib f g μ ν) : IdentDistrib (f ∘ i) g (μ.comap i) ν := by sorry
