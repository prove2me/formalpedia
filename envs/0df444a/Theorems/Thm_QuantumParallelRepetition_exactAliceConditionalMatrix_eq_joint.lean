-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactAliceConditionalMatrix_eq_joint
-- name    : QuantumParallelRepetition.exactAliceConditionalMatrix_eq_joint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T02:45:39.431511+00:00
-- url     : https://prove2.me/theorems/54fb85b7-06e2-45d2-995b-9141c6cc580e
-- title:
--   Alice's conditional operator average equals the Alice marginal of the joint fiber
-- statement:
--   Let $G$ be a finite game with question distribution $\mu$, let $\mu_n$ denote the question distribution of the $n$-fold repetition $G^{n}$ on $X^n \times Y^n$, let $D \subseteq [n]$, and let $\sigma$ be a seed on the remaining coordinates, with distinguished coordinate $i \notin D$, a two-colouring of the remaining coordinates into a left and a right block, orderings of those blocks, and cut points defining a left and a right prefix. Write $\rho_\sigma(\mathbf{x},\mathbf{y})$ for the *revealed history*: the restrictions of $\mathbf{x}$ and $\mathbf{y}$ to $D$, of $\mathbf{x}$ to the left block and to the right prefix, and of $\mathbf{y}$ to the right block and to the left prefix. Fix a history value $h$, questions $x \in X$, $y \in Y$, and set
--   $$\alpha_h(x) = \sum_{\rho_\sigma(\mathbf{x},\mathbf{y}) = h,\ \mathbf{x}_i = x} \mu_n(\mathbf{x},\mathbf{y}), \qquad w_{x,y}(\mathbf{x},\mathbf{y}) = \mu_n(\mathbf{x},\mathbf{y})\,\big[\rho_\sigma(\mathbf{x},\mathbf{y}) = h\big]\big[\mathbf{x}_i = x\big]\big[\mathbf{y}_i = y\big],$$
--   noting that the constraint defining $w_{x,y}$ factorizes into one condition on $\mathbf{x}$ alone and one on $\mathbf{y}$ alone. Let $a_{x,y}(\mathbf{x}) = \sum_{\mathbf{y}} w_{x,y}(\mathbf{x},\mathbf{y})$ be its Alice marginal and $Z_{x,y} = \sum_{\mathbf{x},\mathbf{y}} w_{x,y}(\mathbf{x},\mathbf{y})$ its total mass. The theorem asserts that whenever $Z_{x,y} \neq 0$, for every family of $d \times d$ complex matrices $E(\mathbf{x})$ indexed by $\mathbf{x} \in X^n$,
--   $$\sum_{\rho_\sigma(\mathbf{x},\mathbf{y}) = h,\ \mathbf{x}_i = x} \frac{\mu_n(\mathbf{x},\mathbf{y})}{\alpha_h(x)}\, E(\mathbf{x}) \;=\; \sum_{\mathbf{x} \in X^n} \frac{a_{x,y}(\mathbf{x})}{Z_{x,y}}\, E(\mathbf{x}).$$
--   Equivalently, the operator Alice obtains by averaging $E$ against her posterior on question tuples given $(h,x)$ — a quantity she can compute without knowing $y$ — agrees with the average against the Alice marginal of the two-sided fiber distribution determined by $(x,y)$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L28340-L28421

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_17
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactAliceConditionalMatrix_eq_joint
    {d : Type*} [Fintype d]
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0)
    (E : (Fin n → X) → Matrix d d ℂ) :
    (∑ q : ExactFullQuestion X Y n,
      if exactRevealCode D seed q = history ∧
        q.1 seed.coordinate.val = x
      then
        (exactPriorQuestionWeight G n q /
          exactAliceQuestionMass
            G n D seed history x) • E q.1
      else 0) =
      ∑ xs : Fin n → X,
        (exactFiberAliceMarginal
          G n D seed history x y xs /
          exactFiberQuestionMass
            G n D seed history x y) • E xs := by sorry
