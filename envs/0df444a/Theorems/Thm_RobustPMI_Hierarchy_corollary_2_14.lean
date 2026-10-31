-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_corollary_2_14
-- name    : RobustPMI.Hierarchy.corollary_2_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:05.678756+00:00
-- url     : https://prove2.me/theorems/38f848a6-ac4e-443b-85b5-4dbc727219c5
-- title:
--   Corollary 2.14, p. 9 — moments of a finitely atomic PSD matrix-valued measure on 𝒳 lie in 𝓜^m(G)
-- statement:
--   Let $G(x)$ be a $q\times q$ polynomial matrix and $\mathcal X=\{x:G(x)\succeq0\}$. Let $\Phi=\sum_{i=1}^r W_i\delta_{x^{(i)}}$ be a finitely atomic PSD matrix-valued measure on $\mathcal X$: the points $x^{(i)}\in\mathcal X$ are distinct and the $m\times m$ weights satisfy $W_i\succeq0$. Its moment sequence
--   $$S_\alpha=\int_{\mathcal X}x^\alpha\,d\Phi(x)=\sum_{i=1}^r (x^{(i)})^\alpha W_i,\qquad\alpha\in\mathbb N^n,$$
--   belongs to $\mathcal M^m(G)=\bigcap_{k\ge d_G}\mathcal M^m_k(G)$: for every $k\ge d_G=\lceil\deg(G)/2\rceil$ the matrices $S_\alpha$ ($|\alpha|\le2k$) are symmetric, $M_k(S)\succeq0$ and $M_{k-d_G}(GS)\succeq0$.
--
--   This is the necessary condition of the matrix-valued $\mathcal X$-moment problem. In the convergence analysis it shows that the measure of Proposition 4.1 yields a feasible point of the primal relaxation (4.4) at every order.
--
--   **Formalization Note** The paper states the corollary for any PSD matrix-valued representing measure $\Phi\in\mathfrak M^m_+(\mathcal X)$ (Definition 2.6). Only finitely atomic measures (Definition 2.7) are formalized, which is the only case the proof of Theorem 4.9 uses (the measure $\Phi^\star$ of Proposition 4.1).
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 9, Corollary 2.14 (finitely atomic case, Definition 2.7 p. 7)

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model

namespace RobustPMI.Hierarchy

/-- Corollary 2.14 (p. 9), for a finitely atomic representing measure: the moment sequence
`S_α = ∑_i (x^{(i)})^α W_i` of a finitely atomic PSD matrix-valued measure on `𝒳` lies in
`𝓜^m(G) = ⋂_{k ≥ d_G} 𝓜^m_k(G)`. -/
theorem corollary_2_14 {n m q : ℕ} (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (μ : AtomicMeasure m G) : μ.moments ∈ MMall G := by sorry

end RobustPMI.Hierarchy
