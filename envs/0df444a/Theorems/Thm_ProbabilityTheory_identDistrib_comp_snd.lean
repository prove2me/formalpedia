-- Prove2me | Theorems.Thm_ProbabilityTheory_identDistrib_comp_snd
-- name    : ProbabilityTheory.identDistrib_comp_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:29:31.763798+00:00
-- url     : https://prove2.me/theorems/ea16e2b9-1c9e-4561-a43f-4bc31cf84119
-- title:
--   Probability Theory: ident Distrib comp snd
-- statement:
--   A random variable is identically distributed to its lift to a product space
--   (in the second factor).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L277-L285
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L277-L285

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

theorem ProbabilityTheory.identDistrib_comp_snd {X : Ω
  → α} (hX : Measurable X) (μ : Measure Ω) (μ' : Measure Ω')
  [SigmaFinite μ] [IsProbabilityMeasure μ'] :
    IdentDistrib (X ∘ Prod.snd) X (μ'.prod μ) μ := by sorry
