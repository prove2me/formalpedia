-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Derived_contDiff_M__e4c66d3c2429
-- name    : P2M_FriedCrossing_Derived_contDiff_M__e4c66d3c2429
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:41:23.280546+00:00
-- url     : https://prove2.me/theorems/486b8e7e-0b06-4e2d-b78b-95b0e35848d2
-- title:
--   P2 M Fried Crossing Derived cont Diff M  e4c66d3c2429: P2 M Fried Crossing Derived cont Diff M  e4c66d3c2429
-- statement:
--   The P2 M Fried Crossing Derived cont Diff M  e4c66d3c2429 construction uses the P2 M Fried Crossing Derived cont Diff M  e4c66d3c2429 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L426-L428
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L426-L428

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

theorem P2M_FriedCrossing_Derived_contDiff_M__e4c66d3c2429 (h : ClusterC3 M A) (i j : Fin 2) :
    ContDiff ℝ 2 fun q : ℝ × ℝ => Mτ M q.1 q.2 i j := by sorry

alias «FriedCrossing».«Derived».«contDiff_Mτ» := P2M_FriedCrossing_Derived_contDiff_M__e4c66d3c2429
