-- Prove2me | Theorems.Thm_SphereSOS_Rate_funk_hecke
-- name    : SphereSOS.Rate.funk_hecke
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:20:13.046013+00:00
-- url     : https://prove2.me/theorems/d0562921-a690-49f1-9d7f-0705c8513329
-- title:
--   (8), p. 6 — Funk–Hecke formula: $\int\phi(\langle x,y\rangle)p(y)\,d\sigma(y)=\sum_i\lambda_ip_i(x)$
-- statement:
--   Let $d\ge2$, let $\phi$ be a univariate polynomial with Gegenbauer coefficients $\lambda_i=\lambda_i(\phi)$, and let $p$ be a polynomial whose expansion into spherical harmonics is $p=\sum_{i=0}^Np_i$ on $S^{d-1}$, $p_i\in\mathcal H^d_i$; that is, $p_i$ is the restriction of a homogeneous harmonic polynomial $h_i$ of degree $i$. Then for every $x\in S^{d-1}$,
--   $$\int_{S^{d-1}}\phi(\langle x,y\rangle)\,p(y)\,d\sigma(y)=\sum_{i=0}^N\lambda_i\,p_i(x),$$
--   where $\sigma$ is the rotation-invariant probability measure and $\langle x,y\rangle=\sum_jx_jy_j$.
--
--   The kernel $K(x,y)=\phi(\langle x,y\rangle)$ is therefore diagonal in the harmonic decomposition, with eigenvalue $\lambda_i$ on $\mathcal H^d_i$. Theorem 6 uses it to invert the kernel $q(\langle x,y\rangle)^2$ on a polynomial of degree $2n$.
--
--   **Formalization Note** The paper writes the sum up to $L=\deg\phi$; here it runs over the degrees $0,\dots,N$ present in $p$, and $\lambda_i=0$ for $i>\deg\phi$ by orthogonality, so the two agree. The integral is over $\mathbb R^d$ against $\sigma$, which is concentrated on the sphere.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, pp. 5–6, (8), with the coefficients (9)

import Mathlib
import Definitions.Def_SphereSOS_Rate_Setting
import Definitions.Def_SphereSOS_Rate_Gegenbauer
import Definitions.Def_SphereSOS_Rate_SphereMeasure

namespace SphereSOS.Rate

theorem funk_hecke (d N : ℕ) (hd : 2 ≤ d) (φ : Polynomial ℝ)
    (h : Fin (N + 1) → MvPolynomial (Fin d) ℝ)
    (hhom : ∀ i, (h i).IsHomogeneous (i : ℕ))
    (hharm : ∀ i, laplacian (h i) = 0) :
    ∀ x ∈ sphere d,
      ∫ y : Fin d → ℝ, φ.eval (∑ j, x j * y j) * (∑ i : Fin (N + 1), MvPolynomial.eval y (h i))
          ∂(sigma d) =
        ∑ i : Fin (N + 1), gegCoeff d φ (i : ℕ) * MvPolynomial.eval x (h i) := by sorry

end SphereSOS.Rate
