-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_pullFS_metric_ff1b3d307e09
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_pullFS_metric_ff1b3d307e09
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:34.219542+00:00
-- url     : https://prove2.me/theorems/f619969a-4a5e-4350-8dd5-d08b07296b8a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close pull FS metric ff1b3d307e09: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close pull FS metric ff1b3d307e
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close pull FS metric ff1b3d307e09 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close pull FS metric ff1b3d307e09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L116-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L116-L118

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_pullFS_metric_ff1b3d307e09 (k₀ : ι) (z : Cone n ℂ) :
    (pullFS n k₀).metric z =
      (HermLine.standard (fun _ : Unit ↦ n k₀)).metric (Heights.projBlock k₀ z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«pullFS_metric» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_pullFS_metric_ff1b3d307e09
