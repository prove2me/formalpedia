-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P18_squareRootSandwich_hilbertSchmidtConvergence
-- name    : QAlgorithms.Papers.Independent.Frontier18.P18.squareRootSandwich_hilbertSchmidtConvergence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:09:01.881002+00:00
-- url     : https://prove2.me/theorems/d78966b1-0833-4835-8e52-ebfb1699e916
-- title:
--   Lemma 3: sandwich convergence
-- statement:
--   Let $\mathcal H$ be a nonzero finite dimensional or separable complex Hilbert space. Let $(\rho_n)_{n\geq1}$ be normalized positive trace-class states tending in trace norm to a state $\rho_0$. Let $A_n$ be bounded operators with $\|A_n\|\leq1$ that tend to a bounded operator $A_0$ in the weak operator topology. Then
--
--   $$
--   \left\|\sqrt{\rho_n}A_n\sqrt{\rho_n}-\sqrt{\rho_0}A_0\sqrt{\rho_0}\right\|_2\longrightarrow0,
--   $$
--
--   where $\|\cdot\|_2$ is the Hilbert–Schmidt norm. The operators $A_n$ need not be positive or self-adjoint. This continuity property controls square-root sandwiches when the middle operators converge only weakly.
--
--   **Formalization Note** Lean indexes the approximating sequence by the natural numbers and keeps its limit separate. It encodes the same convergence by the squared Hilbert–Schmidt size tending to zero in the extended nonnegative reals.
-- source:
--   Monotonicity of the Holevo quantity: a necessary condition for equality in terms of a channel and its applications, arXiv:1106.3297v6, PDF p. 21, Lemma 3

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18

noncomputable section

open Filter

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

-- Use the complex unital C-star calculus directly on bounded operators.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Frontier18.P18

open QAlgorithms.RealRegisters (Hilbert)

/-- Lemma 3, PDF pp.21–22. Trace-norm convergence of normalized states and weak
operator convergence of contractions imply Hilbert–Schmidt norm convergence of
the square-root sandwiches. The limit state/operator are indexed separately. -/
theorem squareRootSandwich_hilbertSchmidtConvergence
    {I : Type} [Countable I] [Nonempty I]
    (rho : ℕ → QAlgorithms.Papers.Independent.Dependency50.P33.State I) (rho0 : QAlgorithms.Papers.Independent.Dependency50.P33.State I)
    (hRho : Tendsto (fun n => QAlgorithms.Papers.Independent.Dependency50.P33.traceSize
      ((rho n).coefficients - rho0.coefficients)) atTop (nhds 0))
    (A : ℕ → (Hilbert I →L[ℂ] Hilbert I))
    (A0 : Hilbert I →L[ℂ] Hilbert I)
    (hUnitBall : ∀ n, ‖A n‖ ≤ 1) (hWeak : WeakOperatorConverges A A0) :
    Tendsto (fun n => hilbertSchmidtSizeSq
      ((stateSquareRoot (rho n)).comp ((A n).comp (stateSquareRoot (rho n))) -
        (stateSquareRoot rho0).comp (A0.comp (stateSquareRoot rho0))))
      atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P18

end
