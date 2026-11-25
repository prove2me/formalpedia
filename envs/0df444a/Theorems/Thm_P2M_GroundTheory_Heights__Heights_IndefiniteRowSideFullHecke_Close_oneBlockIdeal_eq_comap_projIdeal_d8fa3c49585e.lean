-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_oneBlockIdeal_eq_comap_projIdeal_d8fa3c49585e
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_oneBlockIdeal_eq_comap_projIdeal_d8fa3c49585e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:25:45.978151+00:00
-- url     : https://prove2.me/theorems/c70e25f7-8276-5fe6-8398-b82aea4ef526
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close one Block Ideal eq comap proj Ideal d8fa3c49585e: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close one
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close one Block Ideal eq comap proj Ideal d8fa3c49585e construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close one Block Ideal eq comap proj Ideal d8fa3c49585e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L81-L86

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_oneBlockIdeal_eq_comap_projIdeal_d8fa3c49585e (P : ArithVariety n) (k₀ : ι) :
    oneBlockIdeal P k₀ = (P.projIdeal k₀).comap (rename (blockCoordEquiv (n := n) k₀)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«oneBlockIdeal_eq_comap_projIdeal» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_oneBlockIdeal_eq_comap_projIdeal_d8fa3c49585e
