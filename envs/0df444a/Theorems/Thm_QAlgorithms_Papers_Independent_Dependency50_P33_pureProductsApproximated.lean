-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P33_pureProductsApproximated
-- name    : QAlgorithms.Papers.Independent.Dependency50.P33.pureProductsApproximated
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:22:20.652027+00:00
-- url     : https://prove2.me/theorems/f13ceb24-1bf8-452e-b85c-21b67f9bc13f
-- title:
--   Pure products are trace-norm limits of noncountably decomposable separable states
-- statement:
--   Let $H$ and $K$ be infinite-dimensional separable complex Hilbert spaces, and let $\alpha$ and $\beta$ be arbitrary pure density operators on them. Write $W$ for the separable density operators on the completed tensor product $H\otimes K$ that admit no countable convex decomposition into product density operators. Then there is a sequence $(\rho_n)_{n\in\mathbb N}$ in $W$ with
--
--   $$
--   \lim_{n\to\infty}\|\rho_n-\alpha\otimes\beta\|_1=0.
--   $$
--
--   Here $\|\cdot\|_1$ is the trace norm. There is no nonvanishing-Fourier hypothesis on the target pure states.
--
--   The result places every pure product in the closure of $W$. It does not assert density of $W$ throughout the separable states, which the source labels a conjecture.
--
--   **Formalization Note** The printed corollary omits the dimension restriction. Its proof identifies both factors with circle $L^2$, and the statement fails with both factors finite-dimensional because $W$ is empty. The infinite-dimensional restriction is therefore recorded explicitly.
-- source:
--   Separability and Entanglement-Breaking in Infinite Dimensions, arXiv:quant-ph/0504204v1, PDF p. 8, Corollary; proof on p.9

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.RealRegisters (Hilbert)

/-- Corollary, PDF pp.8–9: trace-norm approximation of every pure product by
separable states with no countable decomposition.
Printed: no dimension restriction. Changed: both factors are infinite-dimensional,
as used when the proof identifies them with circle L². In finite dimensions the
approximating set is empty. Independent moderation of this correction is pending. -/
theorem pureProductsApproximated {I J : Type} [Countable I] [Countable J]
    [Infinite I] [Infinite J] (a : PureState I) (b : PureState J) :
    ∃ rho : ℕ → State (I × J),
      (∀ n, IsSeparable (rho n).coefficients ∧
        ¬ IsCountablyDecomposable (rho n).coefficients) ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N,
        traceSize ((rho n).coefficients - productCoeff a.val.coefficients b.val.coefficients)
          < ENNReal.ofReal epsilon := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P33

end
