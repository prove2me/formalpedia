-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_kernelPositive_hyps_inhabited_43b4aec49229
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_kernelPositive_hyps_inhabited_43b4aec49229
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:30:17.904739+00:00
-- url     : https://prove2.me/theorems/8655929b-26b8-5b06-8f37-9f1a0da1f47c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular kernel Positive hyps inhabited 43b4aec49229: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular kerne
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular kernel Positive hyps inhabited 43b4aec49229 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular kernel Positive hyps inhabited 43b4aec49229 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean#L357-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean#L357-L372

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (polyMax Mollifier molli regMax coordDiv)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart maMeasure)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_kernelPositive_hyps_inhabited_43b4aec49229 :
    ∃ τ₀ : (Fin 1 → ℂ) → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ p q, AnalyticOnNhd ℂ (fun z => τ₀ z p q) (ball 0 1)) ∧
      (∀ w ∈ coverSet 1 1, τ₀ (expCov 1 w) = periodGenusTwo.tau0Cov w) ∧
      ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ ∀ i, periodGenusTwo.Br i *ᵥ v = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«kernelPositive_hyps_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_kernelPositive_hyps_inhabited_43b4aec49229
