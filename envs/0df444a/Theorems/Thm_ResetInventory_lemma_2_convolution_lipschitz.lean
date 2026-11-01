-- Prove2me | Theorems.Thm_ResetInventory_lemma_2_convolution_lipschitz
-- name    : ResetInventory.lemma_2_convolution_lipschitz
-- status  : Disproved
-- author  : @iris
-- created : 2026-10-31T09:19:42.711687+00:00
-- url     : https://prove2.me/theorems/41a5c344-8d31-40c6-8284-cd9f0d66fe51
-- title:
--   Lemma 2 — Lipschitz bound for a convolution
-- statement:
--   **Lemma 2.** Let $f,g:\mathbb R\to\mathbb R$ with $\int_{-\infty}^{\infty}|f(x)|\,dx<\infty$ and $\int_{-\infty}^{\infty}|g(x)|\,dx<\infty$. Suppose that $f(x)=0$ for $x<0$, that $|f(x)|\le M$ and $|g(x)|\le P$, and that $f$ is Lipschitz with constant $L$ on $x\ge0$. Then the convolution $(f*g)(x)=\int_{-\infty}^{\infty}f(x-z)g(z)\,dz$ is Lipschitz with constant $L\int_{-\infty}^{\infty}|g(z)|\,dz+MP$:
--   $$
--   \big|(f*g)(x)-(f*g)(y)\big|\le\Big(L\int_{-\infty}^{\infty}|g(z)|\,dz+MP\Big)|x-y|\qquad(x,y\in\mathbb R).
--   $$
--   The function $f$ may jump at $0$; the jump costs the term $MP$. In Proposition 2 the demand density plays $f$ and the derivative of the next-period cost-to-go plays $g$, which turns the expected cost-to-go into a function with a Lipschitz derivative.
--
--   Differences from the source:
--   - encoding: ∫|f| and ∫|g| finite → Integrable f and Integrable g (Lebesgue integrable, with a.e. strong measurability); reason: Lean's meaning of a finite Lebesgue integral of |f|; same functions
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, Lemma 2, p.37

import Mathlib

open MeasureTheory

namespace ResetInventory

/-- **Lemma 2** of Lee, Mintz, Aswani, Shen, Yang, arXiv:2209.03571v1, p.37. If `∫|f|` and `∫|g|`
are finite, `f(x) = 0` for `x < 0`, `|f(x)| ≤ M`, `|g(x)| ≤ P`, and `f` is Lipschitz with constant
`L` on `x ≥ 0`, then the convolution `(f ∗ g)(x) = ∫ f(x − z) g(z) dz` is Lipschitz with constant
`L ∫|g(z)| dz + M P`.

**Formalization Note** "`∫|f|` finite" is `Integrable f` (which includes measurability), and the
integrals are over `ℝ` with respect to Lebesgue measure. The Lipschitz conclusion is written as an
explicit inequality for all `x, y`. -/
theorem lemma_2_convolution_lipschitz (f g : ℝ → ℝ) (L M P : ℝ)
    (hf : Integrable f) (hg : Integrable g)
    (hf0 : ∀ x : ℝ, x < 0 → f x = 0)
    (hfM : ∀ x : ℝ, |f x| ≤ M) (hgP : ∀ x : ℝ, |g x| ≤ P)
    (hfL : ∀ x : ℝ, 0 ≤ x → ∀ y : ℝ, 0 ≤ y → |f x - f y| ≤ L * |x - y|) :
    ∀ x y : ℝ, |(∫ z, f (x - z) * g z) - ∫ z, f (y - z) * g z| ≤
      (L * ∫ z, |g z| + M * P) * |x - y| := by sorry

end ResetInventory
