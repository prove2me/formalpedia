-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_diagPeriod_tau0Cov_e3db7c180e1c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_diagPeriod_tau0Cov_e3db7c180e1c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:55.875071+00:00
-- url     : https://prove2.me/theorems/f1583d0d-0616-4f42-898d-3a91b8f1ba48
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular diag Period tau0 Cov e3db7c180e1c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular diag Period tau
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular diag Period tau0 Cov e3db7c180e1c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular diag Period tau0 Cov e3db7c180e1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean#L347-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean#L347-L355

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_diagPeriod_tau0Cov_e3db7c180e1c (g : ℕ) (d : Fin g → ℕ) (w : Fin 1 → ℂ) :
    (diagPeriod g d).tau0Cov w = diagonal (fun _ => Complex.I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«diagPeriod_tau0Cov» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_diagPeriod_tau0Cov_e3db7c180e1c
