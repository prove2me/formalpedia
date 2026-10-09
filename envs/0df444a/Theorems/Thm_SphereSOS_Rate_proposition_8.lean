-- Prove2me | Theorems.Thm_SphereSOS_Rate_proposition_8
-- name    : SphereSOS.Rate.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:32.010277+00:00
-- url     : https://prove2.me/theorems/2fe79162-478a-4512-8b9e-06f82d68d7b5
-- title:
--   Proposition 8, p. 9 — the eigenvalues of $\mathcal T[f]$, $f$ linear, are the $f(x_{\ell+1,i})$ over the roots of $p_{\ell+1}$
-- statement:
--   Let $a<b$, let $w$ be a weight with $w(t)>0$ for $a<t<b$, and let $(p_k)_{k\in\mathbb N}$, $\deg p_k=k$, be orthonormal polynomials for $w$: $\int_a^bp_ip_jw=\delta_{ij}$. For a linear polynomial $f(t)=\alpha+\beta t$ define the $(\ell+1)\times(\ell+1)$ matrix
--   $$\mathcal T[f]_{ij}=\int_a^bp_i(t)p_j(t)f(t)w(t)\,dt\qquad(0\le i,j\le\ell).$$
--   Then the eigenvalues of $\mathcal T[f]$, with multiplicity, are exactly the values $f(x_{\ell+1,i})$, $i=1,\dots,\ell+1$, where $x_{\ell+1,1},\dots,x_{\ell+1,\ell+1}$ are the roots of $p_{\ell+1}$:
--   $$\det\big(X\,I-\mathcal T[f]\big)=\prod_{i=1}^{\ell+1}\big(X-f(x_{\ell+1,i})\big).$$
--
--   For the normalized Gegenbauer family this computes the spectrum of $\mathcal T[h']$ for the tangent line $h'$ of $h$ at $1$.
--
--   **Formalization Note** The conclusion is an identity of characteristic polynomials, the roots of $p_{\ell+1}$ taken with multiplicity in $\mathbb R$; that $p_{\ell+1}$ has $\ell+1$ real roots is part of the claim. The hypotheses are satisfiable, e.g. by the orthonormal Legendre polynomials on $[-1,1]$ with $w=1$.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 9, Proposition 8 and (17)

import Mathlib

namespace SphereSOS.Rate

theorem proposition_8 (a b α β : ℝ) (ℓ : ℕ) (hab : a < b) (w : ℝ → ℝ)
    (hw : ∀ t ∈ Set.Ioo a b, 0 < w t)
    (p : ℕ → Polynomial ℝ)
    (hdeg : ∀ k, (p k).natDegree = k)
    (horth : ∀ i j, ∫ t in a..b, (p i).eval t * (p j).eval t * w t = if i = j then 1 else 0) :
    (Matrix.charpoly (fun i j : Fin (ℓ + 1) =>
        ∫ t in a..b, (p i).eval t * (p j).eval t * (α + β * t) * w t)) =
      ((p (ℓ + 1)).roots.map (fun x => Polynomial.X - Polynomial.C (α + β * x))).prod := by sorry

end SphereSOS.Rate
