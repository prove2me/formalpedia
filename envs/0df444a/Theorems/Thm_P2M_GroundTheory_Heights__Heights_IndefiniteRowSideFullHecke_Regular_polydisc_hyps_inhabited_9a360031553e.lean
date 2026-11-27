-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_polydisc_hyps_inhabited_9a360031553e
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_polydisc_hyps_inhabited_9a360031553e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:26:18.859806+00:00
-- url     : https://prove2.me/theorems/e1a0f784-5c65-53c8-ad46-d6421f0c7149
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular polydisc hyps inhabited 9a360031553e: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular polydisc hyp
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular polydisc hyps inhabited 9a360031553e construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular polydisc hyps inhabited 9a360031553e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean#L273-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean#L273-L278

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_polydisc_hyps_inhabited_9a360031553e (D : ℕ) :
    IsOpen (Set.univ : Set (Fin D → ℂ)) ∧
      ReciprocityTheory.AnForm.A.IsPsh Set.univ (fun z : Fin D → ℂ => ∑ j, ‖z j‖ ^ 2) ∧
      closedBall (0 : Fin D → ℂ) (2 * 1) ⊆ Set.univ ∧ (1 : ℝ) ≤ 1 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) * 1 < 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«polydisc_hyps_inhabited» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_polydisc_hyps_inhabited_9a360031553e
