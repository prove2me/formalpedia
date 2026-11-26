-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Derived_continuousAt_M___1cabb0862b68
-- name    : P2M_FriedCrossing_Derived_continuousAt_M___1cabb0862b68
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:49:49.506817+00:00
-- url     : https://prove2.me/theorems/ad3a0458-45f0-53b5-ad9f-ecc73d3a7b93
-- title:
--   P2 M Fried Crossing Derived continuous At M   1cabb0862b68: P2 M Fried Crossing Derived continuous At M   1cabb0862b68
-- statement:
--   The P2 M Fried Crossing Derived continuous At M   1cabb0862b68 construction uses the P2 M Fried Crossing Derived continuous At M   1cabb0862b68 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L445-L447
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L445-L447

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

theorem P2M_FriedCrossing_Derived_continuousAt_M___1cabb0862b68 (h : ClusterC3 M A) (i j : Fin 2) :
    ContinuousAt (fun q : ℝ × ℝ => Mττ M q.1 q.2 i j) (0, 0) := by sorry

alias «FriedCrossing».«Derived».«continuousAt_Mττ» := P2M_FriedCrossing_Derived_continuousAt_M___1cabb0862b68
