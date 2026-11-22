-- Prove2me | Theorems.Thm_ProbabilityTheory_identDistrib_comp_fst
-- name    : ProbabilityTheory.identDistrib_comp_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:29:27.078417+00:00
-- url     : https://prove2.me/theorems/77356415-8c9d-45a9-899f-815049c9ca16
-- title:
--   Probability Theory: ident Distrib comp fst
-- statement:
--   A random variable is identically distributed to its lift to a product space
--   (in the first factor).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L266-L273
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L266-L273

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Theorems.Thm_ProbabilityTheory_iIndepFun_prod

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
variable [MeasurableSpace α] [MeasurableSpace β]

theorem ProbabilityTheory.identDistrib_comp_fst {X : Ω
  → α} (hX : Measurable X) (μ : Measure Ω) (μ' : Measure Ω')
    [IsProbabilityMeasure μ'] : IdentDistrib (X ∘ Prod.fst) X (μ.prod μ') μ := by sorry
