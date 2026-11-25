-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_hasDerivAt_cutoffDeriv_de17c72e1c35
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_hasDerivAt_cutoffDeriv_de17c72e1c35
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:09:18.710813+00:00
-- url     : https://prove2.me/theorems/5127dd25-42be-46ad-bc22-9decff42e842
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular has Deriv At cutoff Deriv de17c72e1c35: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular has Deriv
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular has Deriv At cutoff Deriv de17c72e1c35 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular has Deriv At cutoff Deriv de17c72e1c35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean#L471-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean#L471-L472

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_hasDerivAt_cutoffDeriv_de17c72e1c35 (s : ℝ) : HasDerivAt cutoffDeriv (cutoffSecondDeriv s) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«hasDerivAt_cutoffDeriv» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_hasDerivAt_cutoffDeriv_de17c72e1c35
