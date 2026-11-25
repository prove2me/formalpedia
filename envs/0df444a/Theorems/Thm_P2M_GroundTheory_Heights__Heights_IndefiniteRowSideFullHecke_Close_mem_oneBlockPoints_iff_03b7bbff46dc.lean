-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_oneBlockPoints_iff_03b7bbff46dc
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_oneBlockPoints_iff_03b7bbff46dc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:47.968723+00:00
-- url     : https://prove2.me/theorems/09ffbd4d-654d-4d55-86b7-2f4d261c1d91
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem one Block Points iff 03b7bbff46dc: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem one Block P
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem one Block Points iff 03b7bbff46dc construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem one Block Points iff 03b7bbff46dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L90-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L90-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_FunFieldEquivMemChartRingIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
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
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_oneBlockPoints_iff_03b7bbff46dc (P : ArithVariety n) (k₀ : ι) (w : Fin (n k₀ + 1) → ℂ) :
    w ∈ oneBlockPoints P k₀ ↔
      (fun _ : Unit ↦ w) ∈ Heights.conePoints (P.projIdeal k₀) ℂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«mem_oneBlockPoints_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_oneBlockPoints_iff_03b7bbff46dc
