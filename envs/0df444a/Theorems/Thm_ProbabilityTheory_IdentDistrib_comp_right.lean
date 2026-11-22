-- Prove2me | Theorems.Thm_ProbabilityTheory_IdentDistrib_comp_right
-- name    : ProbabilityTheory.IdentDistrib.comp_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:23:53.318801+00:00
-- url     : https://prove2.me/theorems/acd5c457-bf96-47d8-8c13-e06b3c875e4b
-- title:
--   Ident Distrib: comp right
-- statement:
--   Composing identically distributed functions with a measurable embedding of conull
--   range
--   gives identically distributed functions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L144-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L144-L147

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Theorems.Thm_ProbabilityTheory_IndepFun_comp_right

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

theorem ProbabilityTheory.IdentDistrib.comp_right {i : δ
  → β} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂ν, a ∈ range i)
    (hg : Measurable g) (hfg : IdentDistrib f g μ ν) : IdentDistrib f (g ∘ i) μ (ν.comap i) := by sorry
