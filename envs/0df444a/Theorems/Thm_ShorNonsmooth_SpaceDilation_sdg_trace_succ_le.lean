-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_trace_succ_le
-- name    : ShorNonsmooth.SpaceDilation.sdg_trace_succ_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T23:11:32.105513+00:00
-- url     : https://prove2.me/theorems/42ad3185-ead6-43f2-9d0c-41c72f0e0abb
-- title:
--   One-step trace increment of A_k^* A_k along a non-stopped SDG run
-- statement:
--   With $T_k = \mathrm{tr}(A_k^* A_k)$, one SDG step from a non-stopped state satisfies $T_{k+1} \le T_k + (\alpha^{*2}-1)d^2/\|\tilde g_k\|^2$. The identity is $T_{k+1} = T_k + (\alpha_{k+1}^2-1)\|A_k^*\xi_{k+1}\|^2$ with $A_k^*\xi_{k+1} = g(x_k)/\|\tilde g_k\|$ since $B_k = A_k^{-1}$; the bound uses $\|g(x_k)\| \le d$ and $\alpha_{k+1} \le \alpha^*$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, proof of Theorem 3.1, p. 53: trace evolution of the accumulated transformation under one dilation step.

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- Shor (1985), proof of Theorem 3.1, p. 53: one-step trace evolution. Since `A_{k+1} = R_{α_{k+1}}(ξ_{k+1}) A_k` and `A_k^* ξ_{k+1} = g(x_k) / ‖g̃_k‖` (because `B_k = A_k^{-1}`), `tr(A_{k+1}^* A_{k+1}) = tr(A_k^* A_k) + (α_{k+1}^2 - 1) ‖g(x_k)‖^2 / ‖g̃_k‖^2`, bounded with `‖g(x_k)‖ ≤ d` and `α_{k+1} ≤ α*`. -/
theorem sdg_trace_succ_le {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (d αstar δ : ℝ) (hd : 0 < d) (hαstar : 0 < αstar) (hδ : 0 < δ)
    (hg : ∀ k : ℕ, ‖g (sdg g h α x₀ B₀ k).x‖ ≤ d)
    (hα : ∀ k : ℕ, 1 ≤ k → 1 + δ ≤ α k ∧ α k ≤ αstar)
    (k : ℕ) (hstop : ∀ j : ℕ, j ≤ k → g (sdg g h α x₀ B₀ j).x ≠ 0)
    (hgT : gTilde g h α x₀ B₀ k ≠ 0) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
        ((LinearMap.adjoint (sdg g h α x₀ B₀ (k + 1)).A.toLinearMap).comp
          (sdg g h α x₀ B₀ (k + 1)).A.toLinearMap) ≤
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
        ((LinearMap.adjoint (sdg g h α x₀ B₀ k).A.toLinearMap).comp
          (sdg g h α x₀ B₀ k).A.toLinearMap) +
        (αstar ^ 2 - 1) * d ^ 2 / ‖gTilde g h α x₀ B₀ k‖ ^ 2 := by sorry

end ShorNonsmooth.SpaceDilation
