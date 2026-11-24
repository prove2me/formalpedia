-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_twistPow_eq_3efc6f400acc
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_twistPow_eq_3efc6f400acc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:07.715809+00:00
-- url     : https://prove2.me/theorems/3ea408fc-cf6f-43c7-a281-33bf196e5288
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close twist Pow eq 3efc6f400acc: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close twist Pow eq 3efc6f400acc
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close twist Pow eq 3efc6f400acc construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close twist Pow eq 3efc6f400acc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L40-L47

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
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_twistPow_eq_3efc6f400acc (M : HermLine n) (p a : ℕ) (C : ℝ) :
    twistPow M p a C =
      (((M.pow p).mul (HermLine.standard n)).pow a).scale (Real.exp (-(a * C))) (Real.exp_pos _) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«twistPow_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_twistPow_eq_3efc6f400acc
