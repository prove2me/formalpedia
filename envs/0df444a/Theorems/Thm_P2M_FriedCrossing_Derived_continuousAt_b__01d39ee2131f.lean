-- Prove2me | Theorems.Thm_P2M_FriedCrossing_Derived_continuousAt_b__01d39ee2131f
-- name    : P2M_FriedCrossing_Derived_continuousAt_b__01d39ee2131f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:50:20.724024+00:00
-- url     : https://prove2.me/theorems/f5dcdcbe-2295-5ca5-95cf-a90144e458bf
-- title:
--   P2 M Fried Crossing Derived continuous At b  01d39ee2131f: P2 M Fried Crossing Derived continuous At b  01d39ee2131f
-- statement:
--   The P2 M Fried Crossing Derived continuous At b  01d39ee2131f construction uses the P2 M Fried Crossing Derived continuous At b  01d39ee2131f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L499-L508
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_cluster_matrices_9_10.lean#L499-L508

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

theorem P2M_FriedCrossing_Derived_continuousAt_b__01d39ee2131f (h : ClusterC3 M A)
    (hsemi : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    ContinuousAt (Function.uncurry (bτ M sStar)) (0, 0) := by sorry

alias «FriedCrossing».«Derived».«continuousAt_bτ» := P2M_FriedCrossing_Derived_continuousAt_b__01d39ee2131f
