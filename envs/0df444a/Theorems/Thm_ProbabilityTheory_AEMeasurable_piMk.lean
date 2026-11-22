-- Prove2me | Theorems.Thm_ProbabilityTheory_AEMeasurable_piMk
-- name    : ProbabilityTheory.AEMeasurable.piMk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:26:10.637061+00:00
-- url     : https://prove2.me/theorems/e0bb9170-9b4b-47be-9870-512ef931b743
-- title:
--   AEMeasurable: pi Mk
-- statement:
--   Move to a different section?
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L184-L191
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L184-L191

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

theorem ProbabilityTheory.AEMeasurable.piMk
    {I : Type*} [Countable I] {F : I → Ω → β} (hF : ∀ i,
  AEMeasurable (F i) μ) :
    AEMeasurable (fun x i => F i x) μ := by sorry
