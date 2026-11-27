-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_twistPow_deg_f99d9fdb283d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_twistPow_deg_f99d9fdb283d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:16:33.416263+00:00
-- url     : https://prove2.me/theorems/81f16900-d844-4ef6-b0a5-b1aef5747636
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close twist Pow deg f99d9fdb283d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close twist Pow deg f99d9fdb283d
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close twist Pow deg f99d9fdb283d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close twist Pow deg f99d9fdb283d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L51-L54

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_twistPow_deg_f99d9fdb283d (M : HermLine n) (p a : ℕ) (C : ℝ) :
    (twistPow M p a C).deg = a • (p • M.deg + (HermLine.standard n).deg) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«twistPow_deg» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_twistPow_deg_f99d9fdb283d
