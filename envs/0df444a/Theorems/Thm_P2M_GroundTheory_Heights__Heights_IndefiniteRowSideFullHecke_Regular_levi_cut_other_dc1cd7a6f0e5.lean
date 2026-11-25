-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_levi_cut_other_dc1cd7a6f0e5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_levi_cut_other_dc1cd7a6f0e5
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:09:14.01452+00:00
-- url     : https://prove2.me/theorems/83488e20-7dfc-47dc-af78-7a77642e82d0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular levi cut other dc1cd7a6f0e5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular levi cut other dc1cd7
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular levi cut other dc1cd7a6f0e5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular levi cut other dc1cd7a6f0e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean#L502-L522
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean#L502-L522

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
open ReciprocityTheory.AnForm.M

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_levi_cut_other_dc1cd7a6f0e5 (y w : Fin 1 → ℂ) (hy : y 0 ≠ 0) :
    levi (fun y : Fin 1 → ℂ => cutG ((‖y 0‖ ^ 2)⁻¹)) y w =
      ((‖y 0‖ ^ 2)⁻¹) ^ 2 * ((‖y 0‖ ^ 2)⁻¹ * cutoffSecondDeriv ((‖y 0‖ ^ 2)⁻¹) + cutoffDeriv ((‖y 0‖ ^ 2)⁻¹)) *
        ‖w 0‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«levi_cut_other» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_levi_cut_other_dc1cd7a6f0e5
