-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Derived_hasDerivAt_M__92e08b1bff5c
-- name    : P2M_FriedCrossing_Derived_hasDerivAt_M__92e08b1bff5c
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:43:20.211657+00:00
-- url     : https://prove2.me/theorems/b19c5126-4bbb-5a2f-9c03-ead7afa654ad
-- title:
--   P2 M Fried Crossing Derived has Deriv At M  92e08b1bff5c: P2 M Fried Crossing Derived has Deriv At M  92e08b1bff5c
-- statement:
--   The P2 M Fried Crossing Derived has Deriv At M  92e08b1bff5c construction uses the P2 M Fried Crossing Derived has Deriv At M  92e08b1bff5c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L439-L443
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L439-L443

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

theorem P2M_FriedCrossing_Derived_hasDerivAt_M__92e08b1bff5c (h : ClusterC3 M A) (θ τ : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => Mτ M θ t i j) (Mττ M θ τ i j) τ := by sorry

alias «FriedCrossing».«Derived».«hasDerivAt_Mτ» := P2M_FriedCrossing_Derived_hasDerivAt_M__92e08b1bff5c
