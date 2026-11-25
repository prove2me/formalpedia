-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_eval_one_scaleHom_ff58bea7d832
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_eval_one_scaleHom_ff58bea7d832
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:23:07.194519+00:00
-- url     : https://prove2.me/theorems/3a605462-d5c7-4d34-b7d4-f83dc93f868e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi Homog eval one scale Hom ff58bea7d832: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi Homog eval one scale Hom ff58bea7d832 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi Homog eval one scale Hom ff58bea7d832 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMultiHomog.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMultiHomog.lean#L64-L68

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
variable {L : Type} [DecidableEq L] {κ : L → Type} {R : Type} [CommRing R]
omit [DecidableEq L]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_eval_one_scaleHom_ff58bea7d832 (φ : MvPolynomial (Σ b, κ b) ℤ →+* R) (f : MvPolynomial (Σ b, κ b) ℤ) :
    eval (fun _ => 1) (scaleHom (L := L) φ f) = φ f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«FlagMultiHomog».«eval_one_scaleHom» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_eval_one_scaleHom_ff58bea7d832
