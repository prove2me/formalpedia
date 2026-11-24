-- Prove2me | Theorems.Thm_ValiantBorder_closedLaurentLowerBound
-- name    : ValiantBorder.closedLaurentLowerBound
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:09:19.196563+00:00
-- url     : https://prove2.me/theorems/a1f23ff3-9a1a-4c9e-9e7a-61996900d0df
-- title:
--   Laurent circuit lower bounds over an algebraically closed field
-- statement:
--   Fix an algebraically closed field $K$. For all sufficiently large $m$, a circuit over $K[\varepsilon,\varepsilon^{-1}]$ that approximates the directed Hamiltonian cycle polynomial needs more than $2^{(\log_2 m)^{4/3}/1600^2}$ gates. The same bound holds for the permanent when $K$ has characteristic different from two. Approximation means that every output coefficient has zero negative powers of $\varepsilon$ and its constant term equals the target coefficient.
--
--   This intermediate bound is used in the proof of [Theorem 1.4](https://hexagonmath.org/2611.00954v1). The [Lean proof](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Approximate.lean#L250-L285) specializes the bound for grid-complete families to these two polynomials.
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, Theorem 1.4 and Appendix N, https://hexagonmath.org/2611.00954v1. Lean, Paper.approx_rate_closed and the Hamiltonian cycle and permanent specializations at lines 250–285, https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Approximate.lean#L250-L285. Underlying conjecture: L. G. Valiant (1979), https://doi.org/10.1145/800135.804419.

import Definitions.Def_VP_VNP_all_fields

theorem ValiantBorder.closedLaurentLowerBound (K : Type) [Field K] [IsAlgClosed K] :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (s : ℕ) (Q : MvPolynomial (Fin m × Fin m) (LaurentPolynomial K)),
      Statement.Computes Q s →
      ((∀ d, (∀ i : ℤ, i < 0 → (MvPolynomial.coeff d Q).coeff i = 0) ∧
          (MvPolynomial.coeff d Q).coeff 0 = MvPolynomial.coeff d (Statement.hc K m)) →
        (2 : ℝ) ^ ((Real.logb 2 m) ^ (4 / 3 : ℝ) / 1600 ^ 2) < s) ∧
      ((2 : K) ≠ 0 → (∀ d, (∀ i : ℤ, i < 0 → (MvPolynomial.coeff d Q).coeff i = 0) ∧
          (MvPolynomial.coeff d Q).coeff 0 = MvPolynomial.coeff d (Statement.perm K m)) →
        (2 : ℝ) ^ ((Real.logb 2 m) ^ (4 / 3 : ℝ) / 1600 ^ 2) < s) := by sorry
