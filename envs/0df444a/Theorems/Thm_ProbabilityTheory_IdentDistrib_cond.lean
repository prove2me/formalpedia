-- Prove2me | Theorems.Thm_ProbabilityTheory_IdentDistrib_cond
-- name    : ProbabilityTheory.IdentDistrib.cond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:26:01.605588+00:00
-- url     : https://prove2.me/theorems/89ef7ab6-d150-4c59-898c-805b21c7e03b
-- title:
--   Ident Distrib: cond
-- statement:
--   The Ident Distrib construction uses the cond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L73-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L73-L108

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

theorem ProbabilityTheory.IdentDistrib.cond
    (hs : MeasurableSet s) (hf' : Measurable f') (hg' : Measurable g')
    (hfg : IdentDistrib (fun a ↦ (f a, f' a)) (fun b ↦ (g b, g' b)) μ ν) :
    IdentDistrib f g (μ[|f' ⁻¹' s]) (ν[|g' ⁻¹' s]) := by sorry
