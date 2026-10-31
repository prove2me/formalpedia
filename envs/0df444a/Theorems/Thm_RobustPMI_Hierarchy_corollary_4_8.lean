-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_corollary_4_8
-- name    : RobustPMI.Hierarchy.corollary_4_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:17.356684+00:00
-- url     : https://prove2.me/theorems/499c1e95-cc49-40da-b9b2-1c4507fbe507
-- title:
--   Corollary 4.8, p. 20 — for every s feasible to (4.5), s_e is feasible to (RPMIO)
-- statement:
--   Suppose $-\theta_1,\dots,-\theta_s$ are SOS-convex and $-P(y,x)$ is PSD-SOS-convex in $y$ for every $x\in\mathcal X$. If $s$ is feasible to the dual relaxation (4.5) at some relaxation order $k$, that is
--   $$s\in\mathcal M_{\lceil k_y/2\rceil}(\Theta),\qquad\mathscr H_s(1)=1,\qquad\mathscr H_s(P(y,x))\in\mathcal Q^m_k(G),$$
--   then its first-order moment vector $s_e=(s_{e_1},\dots,s_{e_\ell})$ satisfies $s_e\in\mathcal Y$ and $P(s_e,x)\succeq0$ for all $x\in\mathcal X$, so $s_e$ is feasible to (RPMIO).
--
--   Every dual-feasible point therefore produces a robustly feasible decision, which is how the hierarchy extracts candidate solutions.
--
--   **Formalization Note** The symmetry of $P$ is a hypothesis ($P\in\mathbb S[y,x]^m$ in the paper). Neither compactness of $\mathcal X$ nor Slater's condition is assumed, as on the page.
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 20, Corollary 4.8

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model

namespace RobustPMI.Hierarchy

/-- Corollary 4.8 (p. 20): if `−θ₁, …, −θ_s` are SOS-convex and `−P(y, x)` is PSD-SOS-convex in `y`
for all `x ∈ 𝒳`, then for every `s` feasible to (4.5), `s_e ∈ 𝒴` and `s_e` is feasible to (RPMIO). -/
theorem corollary_4_8 {ℓ n m q s : ℕ} (f : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP : P.IsSymm) (hθ : ∀ j, IsSOSConvex (-θ j))
    (hPconv : ∀ x ∈ Xset G, IsPSDSOSConvex (-(Patx P x)))
    (k : ℕ) (v : (Fin ℓ →₀ ℕ) → ℝ) (hv : DualFeasible f θ P G k v) :
    sE v ∈ Yset θ ∧ sE v ∈ Feasible θ P G := by sorry

end RobustPMI.Hierarchy
