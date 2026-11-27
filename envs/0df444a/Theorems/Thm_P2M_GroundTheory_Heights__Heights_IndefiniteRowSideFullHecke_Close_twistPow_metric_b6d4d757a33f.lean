-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_twistPow_metric_b6d4d757a33f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_twistPow_metric_b6d4d757a33f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:16:35.811708+00:00
-- url     : https://prove2.me/theorems/9940874c-7e5d-54fd-ad3b-8430be8d8c06
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close twist Pow metric b6d4d757a33f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close twist Pow metric b6d4d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close twist Pow metric b6d4d757a33f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close twist Pow metric b6d4d757a33f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L58-L62

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_twistPow_metric_b6d4d757a33f (M : HermLine n) (p a : ℕ) (C : ℝ) (z : Cone n ℂ) :
    (twistPow M p a C).metric z =
      Real.exp (-(a * C)) * (((M.pow p).mul (HermLine.standard n)).pow a).metric z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«twistPow_metric» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_twistPow_metric_b6d4d757a33f
