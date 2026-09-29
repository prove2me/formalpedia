-- Prove2me | Theorems.Thm_WeightedHilbert_cotangent_bound_of_real
-- name    : WeightedHilbert_cotangent_bound_of_real
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-20T16:41:17.402233+00:00
-- url     : https://prove2.me/theorems/50fb08ae-4896-4acf-bd70-d515c929f92e
-- title:
--   Transfer of a real weighted Hilbert bound to the cotangent kernel
-- statement:
--   Suppose the real weighted Hilbert inequality holds with constant $C$: for every finite family of distinct real frequencies $\lambda_r$, positive admissible gaps $d_r\le |\lambda_r-\lambda_s|$ for $r\ne s$, and complex coefficients $a_r$,
--   $$\left|\sum_{r\ne s}\frac{a_r\overline{a_s}}{\lambda_r-\lambda_s}\right|\le C\sum_r\frac{|a_r|^2}{d_r}.$$
--   Let $\theta_r$ be finitely many real phases, let $a_r$ be complex coefficients, and choose $0<\delta_r\le1$ satisfying $\delta_r\le|\theta_r-\theta_s+m|$ for every $r\ne s$ and every integer $m$. Then
--   $$\left|\sum_{r\ne s}a_r\overline{a_s}\,\pi\cot\bigl(\pi(\theta_r-\theta_s)\bigr)\right|\le C\sum_r\frac{|a_r|^2}{\delta_r}.$$
--   This transfers a real-frequency Hilbert estimate to phases modulo one without increasing the constant when the circle kernel is normalized as $\pi\cot$. It supplies the circle-kernel step in a large-sieve development. The real Hilbert inequality is an explicit premise of this theorem; an accepted platform development provides that premise at a concrete constant.
--
--   Formalization Note: the sums set diagonal terms to zero. The gap assumptions exclude integral differences of distinct phases, and the upper bound $\delta_r\le1$ controls distinct integer translates of the same phase. Empty and one-element index types are permitted.
-- source:
--   Finite-translation derivation using the Cauchy periodization theorem https://prove2.me/theorems/0721e84b-5819-486a-8fca-ceb5c56a8407 and the real weighted Hilbert inequality of Montgomery–Vaughan, Hilbert’s inequality, J. London Math. Soc. (2) 8 (1974), 73–82, Theorem 2. The abstract real premise matches Zeta23.MVDiag: https://prove2.me/theorems/3dc4b7e3-308d-4e47-824a-f875954c6498. This is a derived interface, not a claim of a new mathematical theorem.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
open scoped BigOperators ComplexConjugate

theorem WeightedHilbert_cotangent_bound_of_real (C : ℝ)
    (hH : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (freq δ : κ → ℝ) (v : κ → ℂ),
      Function.Injective freq → (∀ r, 0 < δ r) →
      (∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) →
      ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
        v r * conj (v s) / ((freq r - freq s : ℝ) : ℂ)‖ ≤
          C * ∑ r, ‖v r‖ ^ 2 / δ r)
    {ι : Type} [Fintype ι] [DecidableEq ι] (θ δ : ι → ℝ) (v : ι → ℂ)
    (hpos : ∀ r, 0 < δ r) (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) :
    ‖∑ r : ι, ∑ s : ι, if r = s then (0 : ℂ) else
      v r * conj (v s) * ((Real.pi : ℂ) *
        Complex.cot ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ)))‖ ≤
      C * ∑ r, ‖v r‖ ^ 2 / δ r := by sorry
