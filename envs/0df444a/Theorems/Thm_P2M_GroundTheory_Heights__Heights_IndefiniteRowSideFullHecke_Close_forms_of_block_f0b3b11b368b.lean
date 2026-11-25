-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forms_of_block_f0b3b11b368b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forms_of_block_f0b3b11b368b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:46.90699+00:00
-- url     : https://prove2.me/theorems/3ee1418e-c894-4c40-b9a1-8021bb21eb40
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close forms of block f0b3b11b368b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close forms of block f0b3b11b36
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close forms of block f0b3b11b368b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close forms of block f0b3b11b368b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L107-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L107-L117

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forms_of_block_f0b3b11b368b (k₀ : ι) (m : ℕ) (f : MvPolynomial (Coord n) ℤ)
    (hf : IsWeightedHomogeneous (coordDeg n) f (m • Pi.single k₀ 1)) :
    ∃ f' : MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ,
      IsWeightedHomogeneous (coordDeg (fun _ : Unit ↦ n k₀)) f' (fun _ ↦ m) ∧
        rename (Heights.blockIncl k₀) f' = f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«forms_of_block» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forms_of_block_f0b3b11b368b
