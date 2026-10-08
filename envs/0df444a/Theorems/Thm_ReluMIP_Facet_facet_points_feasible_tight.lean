-- Prove2me | Theorems.Thm_ReluMIP_Facet_facet_points_feasible_tight
-- name    : ReluMIP.Facet.facet_points_feasible_tight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:55.248265+00:00
-- url     : https://prove2.me/theorems/34075df2-59f9-4792-9561-10b56d4f705d
-- title:
--   App. A.2, p. 15 — for small ε > 0 the η + 2 points p⁰, p¹, p̃ⁱ are feasible for (6) and tight on (6b)
-- statement:
--   Let $w\in\mathbb R^\eta$, $b\in\mathbb R$ and $L,U\in\mathbb R^\eta$ with $L_i<U_i$ for every $i$, and assume strict activity, $M^-(f)<0<M^+(f)$ for $f(x)=w\cdot x+b$. Fix $I\subseteq\operatorname{supp}(w)$.
--
--   Then there is $\varepsilon>0$ such that each of the $\eta+2$ points
--   $$
--   p^0=(\breve L,0,0),\quad p^1=(\breve U,f(\breve U),1),\quad \tilde p^i=(\breve L+\varepsilon\sigma_ie^i,0,0)\ (i\notin I),\quad \tilde p^i=(\breve U-\varepsilon\sigma_ie^i,f(\breve U-\varepsilon\sigma_ie^i),1)\ (i\in I)
--   $$
--   is feasible with respect to formulation (6) — it satisfies (6a), every inequality (6b), $x\in[L,U]$, $y\ge0$ and $z\in\{0,1\}$ — and satisfies the inequality (6b) for the subset $I$ at equality. Here $\sigma_i=1$ if $w_i\ge0$ and $\sigma_i=-1$ if $w_i<0$, and $e^i$ is the $i$-th unit vector.
--
--   This is the first half of the proof of Proposition 2: it supplies $\eta+2$ points on the face of (6b).
--
--   **Formalization Note** The page assumes $w\ge 0$ without loss of generality, so that $\breve L=L$, $\breve U=U$ and every step is $+\varepsilon e^i$ from $L$ or $-\varepsilon e^i$ from $U$; the statement is the general-sign version, with $\sigma_i$ the sign by which the step points into the box. Indices are 0-based (`Fin η`).
-- source:
--   arXiv:1811.08359v2, App. A.2 (Proof of Proposition 2), second paragraph, p. 15

import Mathlib
import Definitions.Def_ReluMIP_Facet_Setting

namespace ReluMIP.Facet

/-- App. A.2, p. 15 (arXiv:1811.08359v2): for every `I ⊆ ReluMIP.Ideal.supp(w)` there is a step `ε > 0` such that
each of the `η + 2` points `p⁰, p¹, p̃ⁱ` of `facetPts` is feasible with respect to formulation (6)
and satisfies the inequality (6b) for `I` at equality. -/
theorem facet_points_feasible_tight {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
    (hLU : ∀ i, L i < U i) (hSA : ReluMIP.Ideal.StrictActivity w b L U) :
    ∀ I : Finset (Fin η), I ⊆ ReluMIP.Ideal.supp w → ∃ ε : ℝ, 0 < ε ∧ ∀ j,
      facetPts w b L U I ε j ∈ form6 w b L U ∧
      (facetPts w b L U I ε j).2.1 =
        ReluMIP.Ideal.rhs6b w b L U I (facetPts w b L U I ε j).1 (facetPts w b L U I ε j).2.2 := by sorry

end ReluMIP.Facet
