-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_joint_set_capacity_superadditivity
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.joint_set_capacity_superadditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:57:33.957514+00:00
-- url     : https://prove2.me/theorems/987731af-5e2d-4b4b-b5a8-ca46cf44a532
-- title:
--   §5.4 (62)–(63): superadditivity and optimal-average factorization
-- statement:
--   Let $A,B$ be nonempty marginal state sets, and let $A\otimes B$ be all joint states with marginals in those sets. Including infinite values,
--
--   $$\bar C(A\otimes B)\ge\bar C(A)+\bar C(B).$$
--
--   When both marginal capacities are finite and equality holds, $\Omega(A\otimes B)=\Omega(A)\otimes\Omega(B)$. Strict inequality is possible: for identical infinite-entropy singleton marginals the joint capacity is infinite whereas both singleton capacities are zero. Conversely, even finite joint capacity and a product optimal average do not imply equality: identical uniform rank-two singleton marginals give such a counterexample. This concerns all joint states, rather than a product-state-only set or a tensor channel's output set.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 63, §5.4 (62)–(63): superadditivity and optimal-average factorization

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P18

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState traceSize traceClosure IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasFiniteSupport HasAverage averageCoefficients
   extendedEntropyNats extendedRelativeEntropyNats
   finiteEnsembleCapacity pureStates)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceFirst traceSecond)

namespace QAlgorithms.Papers.Independent.Gap48.P18

attribute [local instance] Classical.propDecidable Classical.decEq

/-- §5.4 (62)–(63): superadditivity and optimal-average factorization, arXiv:quant-ph/0510073v2, PDF pp.63.
The infinite-entropy isomorphic-singleton example is represented with identical coordinate copies. A finite rank-two product-center counterexample witnesses failure of the converse. -/
theorem joint_set_capacity_superadditivity {I J : Type} [Countable I] [Countable J]
    [Nonempty I] [Nonempty J] (A : Set (State I)) (B : Set (State J))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    setChiCapacity A + setChiCapacity B ≤ setChiCapacity (jointMarginalConstraintSet A B) ∧
      (∀ hAB : (jointMarginalConstraintSet A B).Nonempty, setChiCapacity A < ⊤ → setChiCapacity B < ⊤ →
        setChiCapacity (jointMarginalConstraintSet A B) = setChiCapacity A + setChiCapacity B →
        (optimalAverage (jointMarginalConstraintSet A B) hAB).coefficients =
          productCoeff (optimalAverage A hA).coefficients (optimalAverage B hB).coefficients) ∧
      (∀ rho : State I, stateEntropyNats rho = ⊤ → setChiCapacity (couplingSet rho rho) = ⊤ ∧
        setChiCapacity ({rho} : Set (State I)) = 0) ∧
      (∃ (rho : State (Fin 2)) (hC : (couplingSet rho rho).Nonempty),
        rho.coefficients = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
        setChiCapacity ({rho} : Set (State (Fin 2))) = 0 ∧
        0 < setChiCapacity (couplingSet rho rho) ∧ setChiCapacity (couplingSet rho rho) < ⊤ ∧
        (optimalAverage (couplingSet rho rho) hC).coefficients =
          productCoeff rho.coefficients rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
