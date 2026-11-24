-- Prove2me | Theorems.Thm_ValiantBorder_gridLaurentRate
-- name    : ValiantBorder.gridLaurentRate
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:15:08.957472+00:00
-- url     : https://prove2.me/theorems/ba15d415-8b99-4e87-a1f3-0b31c707aa5a
-- title:
--   Laurent circuit lower bound for grid-complete families
-- statement:
--   Fix a field $K$ and a polynomial family grid-complete with some fixed factor. For all sufficiently large $m$, an arithmetic circuit over $K[\varepsilon,\varepsilon^{-1}]$ approximating its size-$m$ polynomial needs more than $2^{(\log_2 m)^{4/3}/1600^2}$ gates. Each coefficient of the circuit output must have zero negative powers of $\varepsilon$ and constant term equal to the target coefficient.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Approximate.lean#L250-L264).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Approximate.lean#L250-L264.

import Definitions.Def_VP_VNP_all_fields
import Definitions.Def_ValiantBorder_gridComplete

theorem ValiantBorder.gridLaurentRate {K : Type} [Field K]
    {G : ∀ m, MvPolynomial (Fin m × Fin m) K} {κ : ℕ} (hG : ValiantBorder.GridComplete K G κ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (s : ℕ) (Q : MvPolynomial (Fin m × Fin m) (LaurentPolynomial K)),
      Statement.Computes Q s →
      (∀ d, (∀ i : ℤ, i < 0 → (MvPolynomial.coeff d Q).coeff i = 0) ∧
        (MvPolynomial.coeff d Q).coeff 0 = MvPolynomial.coeff d (G m)) →
      (2 : ℝ) ^ ((Real.logb 2 m) ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by sorry
