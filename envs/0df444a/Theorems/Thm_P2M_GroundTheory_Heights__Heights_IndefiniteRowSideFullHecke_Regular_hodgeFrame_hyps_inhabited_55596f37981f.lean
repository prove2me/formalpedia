-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_hodgeFrame_hyps_inhabited_55596f37981f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_hodgeFrame_hyps_inhabited_55596f37981f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:25:22.222392+00:00
-- url     : https://prove2.me/theorems/7dc2287c-2580-543a-9987-596527a56d5e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular hodge Frame hyps inhabited 55596f37981f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular hodge Fra
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular hodge Frame hyps inhabited 55596f37981f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular hodge Frame hyps inhabited 55596f37981f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean#L374-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean#L374-L377

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_hodgeFrame_hyps_inhabited_55596f37981f :
    (∀ p q, AnalyticOnNhd ℂ (fun _ : Fin 1 → ℂ => (1 : Matrix (Fin 1) (Fin 1) ℂ) p q) (ball 0 1)) ∧
      (1 : Matrix (Fin 1) (Fin 1) ℂ).rank = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«hodgeFrame_hyps_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_hodgeFrame_hyps_inhabited_55596f37981f
