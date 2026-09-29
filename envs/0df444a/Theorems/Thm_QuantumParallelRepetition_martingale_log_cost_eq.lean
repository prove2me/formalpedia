-- Prove2me | Theorems.Thm_QuantumParallelRepetition_martingale_log_cost_eq
-- name    : QuantumParallelRepetition.martingale_log_cost_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T02:41:19.014642+00:00
-- url     : https://prove2.me/theorems/95e2f89c-235a-4fce-99f1-9f6e26b4dd1c
-- title:
--   The martingale log budget splits into a postselection cost and an answer cost
-- statement:
--   Fix a game $G$, a repetition count $n$, a strategy $S$ for $G^{\otimes n}$, and a set $D\subseteq\{1,\dots,n\}$. Write $p_D$ for the postselection mass, that is the probability, under the outcome law induced by $S$, that the verifier accepts in every coordinate of $D$; and write $N_D=|A|^{|D|}\,|B|^{|D|}$ for the number of joint answer patterns on $D$. If $p_D>0$, then
--
--   $$\log\frac{N_D}{p_D}\;=\;\log\frac{1}{p_D}\;+\;|D|\,\log\big(|A|\,|B|\big).$$
--
--   The two summands on the right are the postselection log-cost and the answer log-cost; the identity is the accounting step that lets the martingale argument treat the single quantity $\log(N_D/p_D)$ as the sum of those two budgets.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L24960-L24986

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_17
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Basic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.martingale_log_cost_eq
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hp : 0 < repeatedPostselectionMass G n S D) :
    Real.log
        (fullHistoryAnswerCount (A := A) (B := B) D /
          repeatedPostselectionMass G n S D) =
      postselectionLogCost G n S D +
        answerLogCost (A := A) (B := B) D := by sorry
