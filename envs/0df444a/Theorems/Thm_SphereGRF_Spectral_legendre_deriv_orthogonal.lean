-- Prove2me | Theorems.Thm_SphereGRF_Spectral_legendre_deriv_orthogonal
-- name    : SphereGRF.Spectral.legendre_deriv_orthogonal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:44.672004+00:00
-- url     : https://prove2.me/theorems/11f387d3-f5cf-47a6-bde6-18edd9de17fc
-- title:
--   Proof of Theorem 3.1, pp. 12–13 — orthogonality of $P_\ell^{(n)}$ in $L^2((1-\mu^2)^n)$, with norm $\frac{2}{2\ell+1}\frac{(\ell+n)!}{(\ell-n)!}$
-- statement:
--   Let $P_\ell$ be the Legendre polynomials and let $n, \ell, \ell' \in \mathbb N_0$ with $n \le \ell$ and $n \le \ell'$. Then
--
--   $$
--   \int_{-1}^1 \Big(\frac{\partial^n}{\partial\mu^n}P_\ell(\mu)\Big)\Big(\frac{\partial^n}{\partial\mu^n}P_{\ell'}(\mu)\Big)(1-\mu^2)^n\,d\mu = \delta_{\ell\ell'}\,\frac{2}{2\ell+1}\,\frac{(\ell+n)!}{(\ell-n)!}.
--   $$
--
--   The $n$-th derivatives of the Legendre polynomials are thus an orthogonal system for the weight $(1-\mu^2)^n$; this is what turns the weighted seminorm $|u|_{V^n(-1,1)}$ into a weighted sum of the Fourier–Legendre coefficients of $u$.
--
--   **Formalization Note** The derivative is the formal derivative of the polynomial $P_\ell$ iterated $n$ times. Since $n \le \ell$, the factorial $(\ell-n)!$ is that of a genuine natural number.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, §3, proof of Theorem 3.1, pp. 12–13, displays following 'This implies that'

import Mathlib
import Definitions.Def_SphereGRF_Spectral_Legendre

namespace SphereGRF.Spectral

/-- Proof of Theorem 3.1, pp. 12–13: for `n ≤ ℓ, ℓ'`,
`∫_{−1}^1 P_ℓ^{(n)}(μ) P_{ℓ'}^{(n)}(μ) (1 − μ²)^n dμ = δ_{ℓℓ'} · 2/(2ℓ+1) · (ℓ+n)!/(ℓ−n)!`. -/
theorem legendre_deriv_orthogonal (n ℓ ℓ' : ℕ) (hℓ : n ≤ ℓ) (hℓ' : n ≤ ℓ') :
    ∫ μ in (-1 : ℝ)..1,
        (Polynomial.derivative^[n] (legendreP ℓ)).eval μ *
          (Polynomial.derivative^[n] (legendreP ℓ')).eval μ * (1 - μ ^ 2) ^ n =
      if ℓ = ℓ' then
        2 / (2 * (ℓ : ℝ) + 1) * ((ℓ + n).factorial : ℝ) / ((ℓ - n).factorial : ℝ)
      else 0 := by sorry

end SphereGRF.Spectral
