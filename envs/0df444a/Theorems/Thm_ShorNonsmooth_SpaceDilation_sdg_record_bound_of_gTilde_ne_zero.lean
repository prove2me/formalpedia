-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_record_bound_of_gTilde_ne_zero
-- name    : ShorNonsmooth.SpaceDilation.sdg_record_bound_of_gTilde_ne_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-04T10:13:49.123368+00:00
-- url     : https://prove2.me/theorems/e8e2e623-d47b-4bb8-ac78-54a91bc00f5b
-- title:
--   Theorem 3.2 core: record bound when no transformed gradient vanishes (Shor 1985, pp. 55-56)
-- statement:
--   Run the SDG method in $E_n$ ($n \ge 1$) with $B_0 = I$, an arbitrary stepsize rule and constant dilation coefficient $\alpha > 1$, with $\|g(x_k)\| \le d$ for all $k$. If no transformed gradient $\tilde g_r$ with $r < k$ vanishes, then for every $k \ge 1$ there is $r < k$ with $\|\tilde g_r\| \le d\sqrt{k(\alpha^2-1)}/\sqrt{\alpha^{2k/n}-1}$. The book normalizes $\xi_r = \tilde g_{r-1}/\|\tilde g_{r-1}\|$, which needs nonvanishing; a vanishing index satisfies the parent bound trivially.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 55-56, proof of Theorem 3.2: normalization step xi_r = gTilde_{r-1}/||gTilde_{r-1}|| requires nonvanishing transformed gradients; hard core isolating the eigenvalue-growth argument from the trivial vanishing case.

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- Shor (1985), pp. 55-56, Theorem 3.2 core under nonvanishing transformed gradients.
Run the SDG method with `B₀ = I`, any stepsize rule `h`, constant coefficients
`α_k = α > 1`, and a selection `g` with `‖g(x_k)‖ ≤ d` for all `k`. If in addition no
transformed gradient `g̃_r` vanishes for `r < k`, then for every `k ≥ 1`,
`min_{0 ≤ r ≤ k-1} ‖g̃_r‖ ≤ d √(k(α² - 1)) / √(α^{2k/n} - 1)`.
The book's proof (pp. 55-56) normalizes `ξ_r = g̃_{r-1} / ‖g̃_{r-1}‖`, which needs
`g̃_r ≠ 0`; when some `g̃_r = 0` the parent bound holds trivially at that index.
This is the hard core of Theorem 3.2: lower bounds on `‖g̃_r‖` control the growth of
the largest eigenvalue of `A_{r+1}` from `A_r` (via `trace_gram_dilate_both`), starting
from `A_0 = I`, and the determinant growth `α^{2k/n}` converts this into the record bound. -/
theorem sdg_record_bound_of_gTilde_ne_zero {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (d α : ℝ) (hd : 0 < d) (hα : 1 < α)
    (hg : ∀ k : ℕ,
      ‖g (sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ _) k).x‖ ≤ d)
    (k : ℕ) (hk : 1 ≤ k)
    (hnez : ∀ r : ℕ, r < k →
      gTilde g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ _) r ≠ 0) :
    ∃ r : ℕ, r < k ∧
      ‖gTilde g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ _) r‖ ≤
        d * Real.sqrt (k * (α ^ 2 - 1)) / Real.sqrt (α ^ ((2 * k : ℝ) / n) - 1) := by sorry

end ShorNonsmooth.SpaceDilation
