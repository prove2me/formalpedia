-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_hermLine_eq_of_a037cafb6bb9
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_hermLine_eq_of_a037cafb6bb9
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:25:46.085505+00:00
-- url     : https://prove2.me/theorems/2a0719a3-9120-4554-bba4-5dd8066bf2c8
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close herm Line eq of a037cafb6bb9: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close herm Line eq of a037cafb
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close herm Line eq of a037cafb6bb9 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close herm Line eq of a037cafb6bb9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L17-L23

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_hermLine_eq_of_a037cafb6bb9 {A B : HermLine n} (hdeg : A.deg = B.deg) (hmet : A.metric = B.metric) :
    A = B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«hermLine_eq_of» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_hermLine_eq_of_a037cafb6bb9
