-- Prove2me | Theorems.Thm_ProbabilityTheory_IdentDistrib_snd_id
-- name    : ProbabilityTheory.IdentDistrib.snd_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:29:31.060829+00:00
-- url     : https://prove2.me/theorems/3da39d29-2aeb-4622-8a81-8582ed150670
-- title:
--   Ident Distrib: snd id
-- statement:
--   The second projection in a product space with measure `μ.prod ν` is distributed like
--   `ν`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L66-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L66-L71

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

theorem ProbabilityTheory.IdentDistrib.snd_id
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IdentDistrib Prod.snd id (μ.prod ν) ν := by sorry
