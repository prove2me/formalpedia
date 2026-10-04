-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_gram_trace_growth
-- name    : ShorNonsmooth.SpaceDilation.sdg_gram_trace_growth
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-04T03:37:06.196644+00:00
-- url     : https://prove2.me/theorems/e5bdf40d-a6b5-4097-a211-9cfbe725954e
-- title:
--   one SDG step from `k-1` to `k` grows the Gram trace by $(\alpha^2-1)\|A_{k-1}\xi\|^2$ (Shor 1985, p. 55)
-- statement:
--   One step of Shor's SDG method dilates the space by $R_{\alpha}(\xi_k)$, so the trace of the Gram operator $A_k A_k$ grows by $(\alpha^2-1)\,\|A_{k-1}\xi_k\|^2$ where $\xi_k$ is the normalised transformed gradient actually chosen by the method. Summing this recurrence over the first $k$ steps, starting from $A_0 = I$, is what bounds the record of transformed-gradient norms in Theorem 3.2.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 55.

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- **The one-step Gram trace growth of Shor (1985), p. 55.** Write `A k` for the
space-transformation operator `A_k` of the SDG state after `k` iterations and `ξ k` for the
direction `ξ_k = g̃ (k-1) / ‖g̃ (k-1)‖` used on step `k`. If the coefficients are the constant
`a > 1` and the method has not stopped at step `k-1`, then

`tr (A k A k) = tr (A (k-1) A (k-1)) + (a^2 - 1) * ‖A (k-1) ξ‖^2`.

This is `trace_mul_dilation` instantiated at the direction the method actually chose,
since `sdgStep` sets `A := dilation (α (k+1)) ξ ∘ A k`. -/
theorem sdg_gram_trace_growth {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (α : ℕ → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : 1 < a)
    (hα : ∀ j : ℕ, 1 ≤ j → α j = a)
    (hg : g (sdg g h α x₀ B₀ (k - 1)).x ≠ 0) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
        ((sdg g h α x₀ B₀ k).A.toLinearMap ∘ₗ (sdg g h α x₀ B₀ k).A.toLinearMap)
      = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
          ((sdg g h α x₀ B₀ (k - 1)).A.toLinearMap ∘ₗ
            (sdg g h α x₀ B₀ (k - 1)).A.toLinearMap) +
        (a ^ 2 - 1) *
          ‖(sdg g h α x₀ B₀ (k - 1)).A
              (‖gTilde g h α x₀ B₀ (k - 1)‖⁻¹ •
                gTilde g h α x₀ B₀ (k - 1))‖ ^ 2 := by
  sorry

end ShorNonsmooth.SpaceDilation
