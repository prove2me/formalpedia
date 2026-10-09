-- Prove2me | Theorems.Thm_SphereGRF_Spectral_weighted_parseval
-- name    : SphereGRF.Spectral.weighted_parseval
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:40:09.516504+00:00
-- url     : https://prove2.me/theorems/4cbdf0df-0adf-483d-80ea-867a89de501c
-- title:
--   Proof of Theorem 3.1, p. 13 — weighted Parseval identity $|u|^2_{V^n} = \sum_{\ell\ge n} u_\ell^2\frac{2\ell+1}{2}\frac{(\ell+n)!}{(\ell-n)!}$
-- statement:
--   Let $u$ be a smooth real function, let $u_\ell = \int_{-1}^1 u(x)P_\ell(x)\,dx$ be its Fourier–Legendre coefficients, and let $n \in \mathbb N_0$. Then
--
--   $$
--   \int_{-1}^1 \Big|\frac{\partial^n}{\partial\mu^n}u(\mu)\Big|^2(1-\mu^2)^n\,d\mu = \sum_{\ell=n}^\infty u_\ell^2\,\frac{2\ell+1}{2}\,\frac{(\ell+n)!}{(\ell-n)!},
--   $$
--
--   both sides being finite or infinite together (the left side is finite for smooth $u$).
--
--   This is the step of the proof of Theorem 3.1 that identifies the $n$-th weighted seminorm with a weighted $\ell^2$ norm of the coefficients; together with the two-sided factorial bound it gives $\|u\|^2_{V^n(-1,1)} \simeq \sum_\ell u_\ell^2 \frac{2\ell+1}{2}(1+\ell^{2n})$.
--
--   **Formalization Note** The paper states the identity for the kernel $k_I = \sum_\ell A_\ell \frac{2\ell+1}{4\pi}P_\ell$, $A_\ell = 2\pi u_\ell$, with the factor $\frac{2\ell+1}{2(4\pi)^2}$. Computing from the orthogonality relation, the factor is $\frac{2(2\ell+1)}{(4\pi)^2}$, which is exactly $\frac{2\ell+1}{2}$ in terms of $u_\ell$; the identity is stated here in the $u_\ell$ form, which is correct. The statement is posed for $u \in C^\infty(\mathbb R)$, the dense class of the definition of $V^n(-1,1)$; the sum is taken in $[0,+\infty]$, and the terms with $\ell < n$ are zero because $\partial^n P_\ell = 0$ then.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, §3, proof of Theorem 3.1, p. 13, display following 'In conclusion we have shown that' (constant corrected)

import Mathlib
import Definitions.Def_SphereGRF_Spectral_WeightedSobolev
import Definitions.Def_SphereGRF_Spectral_FourierLegendre

open scoped ENNReal ContDiff

namespace SphereGRF.Spectral

/-- Proof of Theorem 3.1, p. 13 (first display, constant corrected): for smooth `u` and every
`n`, `∫_{−1}^1 |u^{(n)}(μ)|² (1 − μ²)^n dμ = Σ_{ℓ ≥ n} u_ℓ² (2ℓ+1)/2 · (ℓ+n)!/(ℓ−n)!`. -/
theorem weighted_parseval (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) (n : ℕ) :
    ENNReal.ofReal (wSemi n u) =
      ∑' ℓ : ℕ,
        if n ≤ ℓ then
          ENNReal.ofReal (legendreCoeff u ℓ ^ 2 * ((2 * (ℓ : ℝ) + 1) / 2) *
            (((ℓ + n).factorial : ℝ) / ((ℓ - n).factorial : ℝ)))
        else 0 := by sorry

end SphereGRF.Spectral
