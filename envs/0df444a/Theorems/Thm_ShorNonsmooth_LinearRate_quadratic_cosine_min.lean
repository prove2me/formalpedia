-- Prove2me | Theorems.Thm_ShorNonsmooth_LinearRate_quadratic_cosine_min
-- name    : ShorNonsmooth.LinearRate.quadratic_cosine_min
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T11:44:09.865172+00:00
-- url     : https://prove2.me/theorems/8f277dd6-2864-4f79-ae14-55d748b6a073
-- title:
--   Example (p. 33) — $\min_{x \ne 0} (Ax,x)/(\|Ax\|\|x\|) = 2\sqrt{\lambda\mu}/(\lambda+\mu)$ for positive definite $A$
-- statement:
--   Let $A$ be a symmetric positive definite linear operator on $E_n$ with smallest eigenvalue $\lambda > 0$ and largest eigenvalue $\mu$; that is, $\lambda\|x\|^2 \le (Ax, x) \le \mu\|x\|^2$ for all $x$, and there are unit vectors $s_1, s_2$ with $As_1 = \lambda s_1$, $As_2 = \mu s_2$. For the quadratic form $f(x) = \tfrac12(Ax, x)$ one has $g_f(x) = Ax$, and the cosine of the angle between $g_f(x)$ and $x$ satisfies
--   $$
--   \min_{x \in E_n,\ x \ne 0} \frac{(Ax, x)}{\|Ax\|\,\|x\|} = \frac{2\sqrt{\lambda\mu}}{\lambda + \mu};
--   $$
--   moreover, if $s_1$ and $s_2$ are orthonormal, the minimum is attained at
--   $$
--   x = \sqrt{\frac{\mu}{\lambda+\mu}}\, s_1 + \sqrt{\frac{\lambda}{\lambda+\mu}}\, s_2 .
--   $$
--
--   Hence a positive definite quadratic satisfies (2.12) with $\cos\varphi = 2\sqrt{\lambda\mu}/(\lambda+\mu)$, $\sin\varphi = (\mu-\lambda)/(\mu+\lambda)$, and Theorem 2.7 gives linear convergence with ratio $(\varrho - 1)/(\varrho + 1)$, $\varrho = \mu/\lambda$ the condition number.
--
--   **Formalization Note** The eigenvalues are pinned by the two quadratic-form bounds together with the eigenvector equations, so $\lambda$ is the smallest and $\mu$ the largest eigenvalue. The minimum is stated as `IsLeast` (value attained), not as an infimum. The attaining point is asserted under the hypothesis $(s_1, s_2) = 0$, which holds automatically when $\lambda < \mu$; when $\lambda = \mu$ every nonzero $x$ attains the minimum $1$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 33–34, Example (unnumbered display following (2.23))

import Mathlib

namespace ShorNonsmooth.LinearRate

/-- Shor (1985), pp. 33–34, Example (unnumbered display). Let `A` be a symmetric positive
definite operator on `E_n` with smallest eigenvalue `λ > 0` and largest eigenvalue `μ`
(so `λ‖x‖² ≤ (Ax, x) ≤ μ‖x‖²`, with unit eigenvectors `s₁`, `s₂` for `λ` and `μ`). Then
`min_{x ≠ 0} (Ax, x)/(‖Ax‖ ‖x‖) = 2√(λμ)/(λ + μ)`, and, when `s₁ ⊥ s₂`, the minimum is attained
at `x = √(μ/(λ + μ)) s₁ + √(λ/(λ + μ)) s₂`. -/
theorem quadratic_cosine_min {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (hA : A.IsSymmetric)
    (lam mu : ℝ) (hlam : 0 < lam)
    (hlow : ∀ x, lam * ‖x‖ ^ 2 ≤ inner ℝ (A x) x)
    (hup : ∀ x, inner ℝ (A x) x ≤ mu * ‖x‖ ^ 2)
    (s₁ s₂ : EuclideanSpace ℝ (Fin n)) (hs₁ : ‖s₁‖ = 1) (hs₂ : ‖s₂‖ = 1)
    (hAs₁ : A s₁ = lam • s₁) (hAs₂ : A s₂ = mu • s₂) :
    IsLeast {c : ℝ | ∃ x : EuclideanSpace ℝ (Fin n), x ≠ 0 ∧
        c = inner ℝ (A x) x / (‖A x‖ * ‖x‖)}
      (2 * Real.sqrt (lam * mu) / (lam + mu)) ∧
    (inner ℝ s₁ s₂ = (0 : ℝ) →
      let x := Real.sqrt (mu / (lam + mu)) • s₁ + Real.sqrt (lam / (lam + mu)) • s₂
      inner ℝ (A x) x / (‖A x‖ * ‖x‖) = 2 * Real.sqrt (lam * mu) / (lam + mu)) := by sorry

end ShorNonsmooth.LinearRate
