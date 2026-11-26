-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Derived_continuousAt_a__6cdfbca45661
-- name    : P2M_FriedCrossing_Derived_continuousAt_a__6cdfbca45661
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:50:13.341871+00:00
-- url     : https://prove2.me/theorems/db29c4d5-e69c-5199-a98d-fd54aaca89ea
-- title:
--   P2 M Fried Crossing Derived continuous At a  6cdfbca45661: P2 M Fried Crossing Derived continuous At a  6cdfbca45661
-- statement:
--   The P2 M Fried Crossing Derived continuous At a  6cdfbca45661 construction uses the P2 M Fried Crossing Derived continuous At a  6cdfbca45661 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L493-L497
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L493-L497

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}

theorem P2M_FriedCrossing_Derived_continuousAt_a__6cdfbca45661 (h : ClusterC3 M A) : ContinuousAt (Function.uncurry (aτ M)) (0, 0) := by sorry

alias «FriedCrossing».«Derived».«continuousAt_aτ» := P2M_FriedCrossing_Derived_continuousAt_a__6cdfbca45661
