-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_upperBounds_eq_of_sSup_eq_1bfc466c0f85
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_upperBounds_eq_of_sSup_eq_1bfc466c0f85
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:34.029435+00:00
-- url     : https://prove2.me/theorems/fbc010e6-b71b-41f3-b995-801f5f2578bc
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close upper Bounds eq of s Sup eq 1bfc466c0f85: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close upper Bounds
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close upper Bounds eq of s Sup eq 1bfc466c0f85 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close upper Bounds eq of s Sup eq 1bfc466c0f85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L180-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L180-L187

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_upperBounds_eq_of_sSup_eq_1bfc466c0f85 {s t : Set ℝ} (hs : BddAbove s) (ht : BddAbove t)
    (hne : s.Nonempty ↔ t.Nonempty) (h : sSup s = sSup t) : upperBounds s = upperBounds t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«upperBounds_eq_of_sSup_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_upperBounds_eq_of_sSup_eq_1bfc466c0f85
