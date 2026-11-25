-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_eval__genPt_365ba5726aa3
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_eval__genPt_365ba5726aa3
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:23:29.144183+00:00
-- url     : https://prove2.me/theorems/c31264a2-e13c-41cb-aed0-9137f5fd6fae
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi Homog eval  gen Pt 365ba5726aa3: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi Homog eval  gen Pt 365ba5726aa3 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi Homog eval  gen Pt 365ba5726aa3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMultiHomog.lean#L125-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMultiHomog.lean#L125-L131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMultiHomog
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {N1 n : ℕ}
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_eval__genPt_365ba5726aa3 (P : Ideal (MRing ι)) {S : Type} [CommRing S] (φ : FnField P →+* S) (f : MRing ι) :
    eval₂ (Int.castRingHom S) (fun p => φ (genPt P p)) f =
      φ (algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P f)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«FlagMultiHomog».«eval₂_genPt» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_eval__genPt_365ba5726aa3
