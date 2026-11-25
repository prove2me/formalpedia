-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_sameOrbit_liftAt_1a859d9855f3
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_sameOrbit_liftAt_1a859d9855f3
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:50:36.785046+00:00
-- url     : https://prove2.me/theorems/3b732a70-c879-5265-822f-84548147635b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Res same Orbit lift At 1a859d9855f3: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Res same Orbit li
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Res same Orbit lift At 1a859d9855f3 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Res same Orbit lift At 1a859d9855f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FourierIntegralBound.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FourierIntegralBound.lean#L78-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial MeasureTheory Topology Filter Set
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential MIntegrable locDens)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res
variable {P : Ideal (MRing ι ℂ)} {e : ℕ} (R : Res ι P e)
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_sameOrbit_liftAt_1a859d9855f3 {x x' y : R.R.M} (hy : y ∈ R.R.src (R.idx x))
    (hy' : y ∈ R.R.src (R.idx x')) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ R.liftAt x y = tsmul c (R.liftAt x' y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«Res».«sameOrbit_liftAt» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_sameOrbit_liftAt_1a859d9855f3
