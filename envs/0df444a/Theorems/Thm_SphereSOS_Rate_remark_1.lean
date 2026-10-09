-- Prove2me | Theorems.Thm_SphereSOS_Rate_remark_1
-- name    : SphereSOS.Rate.remark_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:33.532235+00:00
-- url     : https://prove2.me/theorems/1c5382d1-e872-4dc7-8e69-c24a13aa2e8a
-- title:
--   Remark 1, p. 6 — if $\phi\ge0$ on $[-1,1]$ then $\lambda_i\le\lambda_0$
-- statement:
--   Let $d\ge2$ and let $\phi$ be a univariate polynomial of degree $L$ with $\phi(t)\ge0$ for all $t\in[-1,1]$. Then its Gegenbauer coefficients (9) satisfy
--   $$\lambda_i\le\lambda_0\qquad(i=0,\dots,L).$$
--
--   Applied to $\phi=q^2$ normalized by $\lambda_0=1$, this gives $\lambda_{2k}\le1$, which is used in Proposition 9.
--
--   **Formalization Note** $L$ is `φ.natDegree`, and $i$ ranges over $0,\dots,L$ as on the page.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 6, Remark 1

import Mathlib
import Definitions.Def_SphereSOS_Rate_Gegenbauer

namespace SphereSOS.Rate

theorem remark_1 (d i : ℕ) (hd : 2 ≤ d) (φ : Polynomial ℝ)
    (hφ : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ φ.eval t)
    (hi : i ≤ φ.natDegree) :
    gegCoeff d φ i ≤ gegCoeff d φ 0 := by sorry

end SphereSOS.Rate
