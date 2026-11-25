-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_eval_tsmul_of_isMultiHomog_ed52743cf4a4
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_eval_tsmul_of_isMultiHomog_ed52743cf4a4
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:51:54.128876+00:00
-- url     : https://prove2.me/theorems/a7820a74-7649-463c-bd08-68a54542feca
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter eval tsmul of is Multi Homog ed52743cf4a4: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter eval tsmul
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter eval tsmul of is Multi Homog ed52743cf4a4 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter eval tsmul of is Multi Homog ed52743cf4a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FourierIntegralBound.lean#L20-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FourierIntegralBound.lean#L20-L41

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_eval_tsmul_of_isMultiHomog_ed52743cf4a4 {s : MRing ι ℂ} {a : K → ℕ} (hs : IsMultiHomog s a)
    (c : K → ℂ) (z : MCone ι) :
    eval (tsmul c z) s = (∏ k, c k ^ a k) * eval z s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«eval_tsmul_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_eval_tsmul_of_isMultiHomog_ed52743cf4a4
