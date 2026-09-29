-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactFixedAliceQuestionMass_eq_product
-- name    : QuantumParallelRepetition.exactFixedAliceQuestionMass_eq_product
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T06:39:48.543379+00:00
-- url     : https://prove2.me/theorems/791f9089-7b8a-4697-a1af-328c0a2eddf8
-- title:
--   Marginalising the repeated question distribution over Alice's free coordinates factorises
-- statement:
--   Let $G$ be a game with question distribution $\mu(x,y)$ on $X\times Y$, and write $\mu_Y(y)=\sum_{x\in X}\mu(x,y)$ for its $Y$-marginal. The $n$-fold repetition $G^{n}$ carries the product question distribution $\mu^{\otimes n}(\mathbf x,\mathbf y)=\prod_{j=1}^{n}\mu(x_j,y_j)$. Fix a set of coordinates $F\subseteq\{1,\dots,n\}$, a tuple $\mathbf u\in X^{n}$ of prescribed Alice questions, and a tuple $\mathbf y\in Y^{n}$ of Bob questions, and consider the mass
--   $$Z\;=\;\sum_{\mathbf x\in X^{n}}\mathbf 1\big[\,x_j=u_j\ \text{for all }j\in F\,\big]\;\mu^{\otimes n}(\mathbf x,\mathbf y)$$
--   obtained by summing the repeated question weight over all Alice tuples that agree with $\mathbf u$ on $F$. The theorem states that this mass factorises over coordinates,
--   $$Z\;=\;\prod_{j=1}^{n}\begin{cases}\mu(u_j,y_j), & j\in F,\\[2pt] \mu_Y(y_j), & j\notin F,\end{cases}$$
--   so that every pinned coordinate contributes its joint weight while every free coordinate contributes only the $Y$-marginal. It is the elementary product formula that underlies all later computations of conditional question masses for the repeated game.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L28698-L28757

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_17
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactFixedAliceQuestionMass_eq_product
    (G : Game X Y A B) (n : ℕ)
    (fixed : Finset (Fin n))
    (known : Fin n → X) (ys : Fin n → Y) :
    exactFixedAliceQuestionMass G n fixed known ys =
      ∏ j : Fin n,
        if j ∈ fixed then G.questionWeight (known j) (ys j)
        else G.marginalY (ys j) := by sorry
