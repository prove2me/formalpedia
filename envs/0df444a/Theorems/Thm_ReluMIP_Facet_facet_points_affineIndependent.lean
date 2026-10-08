-- Prove2me | Theorems.Thm_ReluMIP_Facet_facet_points_affineIndependent
-- name    : ReluMIP.Facet.facet_points_affineIndependent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:50.537061+00:00
-- url     : https://prove2.me/theorems/2eafce49-7218-4576-a7d0-2a00b4f76910
-- title:
--   App. A.2, p. 15 — the η + 2 points p⁰, p¹, p̃ⁱ are affinely independent
-- statement:
--   Let $w\in\mathbb R^\eta$, $b\in\mathbb R$, $L,U\in\mathbb R^\eta$, a subset $I\subseteq\operatorname{supp}(w)$ and a step $\varepsilon>0$. Then the $\eta+2$ points
--   $$
--   p^0=(\breve L,0,0),\quad p^1=(\breve U,f(\breve U),1),\quad \tilde p^i=(\breve L+\varepsilon\sigma_ie^i,0,0)\ (i\notin I),\quad \tilde p^i=(\breve U-\varepsilon\sigma_ie^i,f(\breve U-\varepsilon\sigma_ie^i),1)\ (i\in I)
--   $$
--   of $\mathbb R^\eta\times\mathbb R\times\mathbb R$ are affinely independent. Here $f(x)=w\cdot x+b$, $\sigma_i=1$ if $w_i\ge0$ and $\sigma_i=-1$ if $w_i<0$, and $e^i$ is the $i$-th unit vector.
--
--   Together with the feasibility and tightness of these points, this shows that the face of $\operatorname{conv}$ of the points of (6) cut out by (6b) has dimension at least $\eta+1$.
--
--   **Formalization Note** The page proves this for the $\varepsilon$ chosen in the previous step, with $w\ge0$; the statement here holds for every $\varepsilon>0$ and every sign pattern, and needs neither the bounds $L<U$ nor strict activity (the page's matrix argument uses neither). Indices are 0-based (`Fin η`); the points are indexed by `Fin 2 ⊕ Fin η`.
-- source:
--   arXiv:1811.08359v2, App. A.2 (Proof of Proposition 2), third paragraph and the matrix argument, p. 15

import Mathlib
import Definitions.Def_ReluMIP_Facet_Setting

namespace ReluMIP.Facet

/-- App. A.2, p. 15 (arXiv:1811.08359v2): for every `I ⊆ ReluMIP.Ideal.supp(w)` and every step `ε > 0`, the
`η + 2` points `p⁰, p¹, p̃ⁱ` of `facetPts` are affinely independent. -/
theorem facet_points_affineIndependent {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
    (I : Finset (Fin η)) (hI : I ⊆ ReluMIP.Ideal.supp w) (ε : ℝ) (hε : 0 < ε) :
    AffineIndependent ℝ (facetPts w b L U I ε) := by sorry

end ReluMIP.Facet
