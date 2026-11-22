-- Prove2me | Theorems.Thm_ProbabilityTheory_IdentDistrib_fst_id
-- name    : ProbabilityTheory.IdentDistrib.fst_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:29:31.618808+00:00
-- url     : https://prove2.me/theorems/87a680a0-1cde-4a95-9c58-4595bf485568
-- title:
--   Ident Distrib: fst id
-- statement:
--   The first projection in a product space with measure `μ.prod ν` is distributed like `μ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L55-L60
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L55-L60

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
open ProbabilityTheory
variable {μ : Measure α} {ν : Measure β} {f f' : α → γ} {g g' : β → γ} {s : Set γ}

theorem ProbabilityTheory.IdentDistrib.fst_id
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure ν] :
    IdentDistrib Prod.fst id (μ.prod ν) μ := by sorry
