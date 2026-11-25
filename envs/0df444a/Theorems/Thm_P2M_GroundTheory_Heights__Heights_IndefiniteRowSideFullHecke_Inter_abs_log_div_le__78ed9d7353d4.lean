-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_abs_log_div_le__78ed9d7353d4
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_abs_log_div_le__78ed9d7353d4
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:49:52.905355+00:00
-- url     : https://prove2.me/theorems/c5e95dd9-21c8-5b5b-acce-862d2e8ad3ce
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter abs log div le  78ed9d7353d4: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter abs log div le  78ed9d73
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter abs log div le  78ed9d7353d4 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter abs log div le  78ed9d7353d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FourierIntegralBound.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FourierIntegralBound.lean#L58-L63

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_abs_log_div_le__78ed9d7353d4 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    |Real.log (a / b)| ≤ |Real.log a| + |Real.log b| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«abs_log_div_le'» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_abs_log_div_le__78ed9d7353d4
