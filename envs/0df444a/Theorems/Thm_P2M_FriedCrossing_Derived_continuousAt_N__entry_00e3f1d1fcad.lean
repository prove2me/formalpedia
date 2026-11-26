-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Derived_continuousAt_N__entry_00e3f1d1fcad
-- name    : P2M_FriedCrossing_Derived_continuousAt_N__entry_00e3f1d1fcad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:43:53.626484+00:00
-- url     : https://prove2.me/theorems/8a9c7a15-2c36-433b-afd6-35701ded3fc7
-- title:
--   P2 M Fried Crossing Derived continuous At N  entry 00e3f1d1fcad: P2 M Fried Crossing Derived continuous At N  entry 00e3f1d1fcad
-- statement:
--   The P2 M Fried Crossing Derived continuous At N  entry 00e3f1d1fcad construction uses the P2 M Fried Crossing Derived continuous At N  entry 00e3f1d1fcad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L487-L491
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L487-L491

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

theorem P2M_FriedCrossing_Derived_continuousAt_N__entry_00e3f1d1fcad (h : ClusterC3 M A) (i j : Fin 2) :
    ContinuousAt (fun q : ℝ × ℝ => Nτ M q.1 q.2 i j) (0, 0) := by sorry

alias «FriedCrossing».«Derived».«continuousAt_Nτ_entry» := P2M_FriedCrossing_Derived_continuousAt_N__entry_00e3f1d1fcad
