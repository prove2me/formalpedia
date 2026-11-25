-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_locDens_congr_germ_cdbb9f70069d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_locDens_congr_germ_cdbb9f70069d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:59:41.383327+00:00
-- url     : https://prove2.me/theorems/9c990aa7-87aa-5148-a71c-876c43f41ac3
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter loc Dens congr germ cdbb9f70069d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter loc Dens congr germ
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter loc Dens congr germ cdbb9f70069d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter loc Dens congr germ cdbb9f70069d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PZIntAdd.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PZIntAdd.lean#L18-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StZIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PZIntAdd
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
open ReciprocityTheory.AnForm.M Topology
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_locDens_congr_germ_cdbb9f70069d {n : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas n X)
    (Φ Ψ : Fin n → LocPot X) (j : Fin A.n) (y : Fin n → ℂ)
    (h : ∀ k, (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
      (fun y' => (Ψ k).φ ((A.chart j).symm y) ((A.chart j).symm y'))) :
    locDens A Φ j y = locDens A Ψ j y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«locDens_congr_germ» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_locDens_congr_germ_cdbb9f70069d
