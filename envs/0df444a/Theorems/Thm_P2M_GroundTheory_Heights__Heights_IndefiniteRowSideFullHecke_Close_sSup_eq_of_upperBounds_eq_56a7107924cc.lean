-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_sSup_eq_of_upperBounds_eq_56a7107924cc
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_sSup_eq_of_upperBounds_eq_56a7107924cc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:08.93639+00:00
-- url     : https://prove2.me/theorems/f86238e1-58d0-423b-a73a-5f91d724f849
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close s Sup eq of upper Bounds eq 56a7107924cc: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close s Sup eq of
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close s Sup eq of upper Bounds eq 56a7107924cc construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close s Sup eq of upper Bounds eq 56a7107924cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L156-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L156-L178

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (secM sec IsMultiHomog)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_sSup_eq_of_upperBounds_eq_56a7107924cc {s t : Set ℝ} (h : upperBounds s = upperBounds t) :
    sSup s = sSup t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«sSup_eq_of_upperBounds_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_sSup_eq_of_upperBounds_eq_56a7107924cc
