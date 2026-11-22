-- Prove2me | Theorems.Thm_ProbabilityTheory_identDistrib_map
-- name    : ProbabilityTheory.identDistrib_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:26:12.351946+00:00
-- url     : https://prove2.me/theorems/0fa67e69-690d-42d6-8591-eb1ecc499ef9
-- title:
--   Probability Theory: ident Distrib map
-- statement:
--   A random variable is identically distributed to its pullbacks.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L225-L229
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L225-L229

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
variable [MeasurableSpace α] [MeasurableSpace β]

theorem ProbabilityTheory.identDistrib_map {X : Ω → α} (hX : Measurable X) {f : α → β} (hf : Measurable f)
    (μ : Measure Ω) : IdentDistrib f (f ∘ X) (μ.map X) μ := by sorry
