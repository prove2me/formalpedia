-- Prove2me | Theorems.Thm_WeightedHilbert_circle_cosecant_bound_sixteen
-- name    : WeightedHilbert_circle_cosecant_bound_sixteen
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-20T17:01:48.371974+00:00
-- url     : https://prove2.me/theorems/de62b18a-6cc5-46cb-9555-8b45ad09f4bf
-- title:
--   Weighted circle Hilbert inequality with an explicit constant
-- statement:
--   Let $\theta_r$ be a finite family of real phases, let $a_r$ be complex coefficients, and let $0<\delta_r\le1$. Suppose that distinct phases are separated modulo one in the precise sense
--   $$\delta_r\le |\theta_r-\theta_s+m|\quad(r\ne s,\ m\in\mathbb Z).$$
--   Then the off-diagonal cosecant quadratic form satisfies
--   $$\left|\sum_{r\ne s}\frac{a_r\overline{a_s}}{\sin\bigl(\pi(\theta_r-\theta_s)\bigr)}\right|\le16\sum_r\frac{|a_r|^2}{\delta_r}.$$
--   This is a nonuniform circle Hilbert inequality with an explicit, nonsharp constant. The individual gaps allow it to feed weighted large-sieve estimates for rational frequencies with different denominators. Real phase representatives are retained because the cosecant kernel is anti-periodic.
--
--   Formalization Note: the diagonal is set to zero, and the gap hypothesis guarantees that every off-diagonal sine denominator is nonzero. Empty and singleton index types are included.
-- source:
--   Derived circle version of Montgomery–Vaughan, Hilbert’s inequality, J. London Math. Soc. (2) 8 (1974), 73–82, Theorem 2. Uses the accepted real constant-13 estimate https://prove2.me/theorems/a4129486-dfa9-453b-aded-7a7f80df65d7 and spectral reduction https://prove2.me/theorems/ba4fc2f1-1747-48dd-89db-fe2cde52c5ac, transferred by https://prove2.me/theorems/50fb08ae-4896-4acf-bd70-d515c929f92e and the elementary identity csc(z)=cot(z/2)-cot(z). Constant 16 is a proved coarse consequence, not the sharp constant quoted from the original paper.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
open scoped BigOperators ComplexConjugate

theorem WeightedHilbert_circle_cosecant_bound_sixteen {ι : Type} [Fintype ι] [DecidableEq ι]
    (θ δ : ι → ℝ) (v : ι → ℂ)
    (hpos : ∀ r, 0 < δ r) (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) :
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
      v r * conj (v s) /
        Complex.sin ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ))‖ ≤
      16 * ∑ r, ‖v r‖ ^ 2 / δ r := by sorry
