-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_proposition_4_1
-- name    : RobustPMI.Hierarchy.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:04.787371+00:00
-- url     : https://prove2.me/theorems/c0dc62a9-1edf-4894-b1bf-8648df89ff53
-- title:
--   Proposition 4.1, p. 17 — a finitely atomic Lagrangian measure Φ⋆ with f⋆ = inf_𝒴 f − 𝓛_{Φ⋆}(P)
-- statement:
--   Consider (RPMIO): minimize $f(y)$ over $y\in\mathcal Y$ subject to $P(y,x)\succeq0$ for all $x\in\mathcal X$, with optimal value $f^\star$, and suppose it has an optimal solution. Under Assumption 1 (SOS-convexity of $f$ and $-\theta_j$, PSD-SOS-convexity of $-P(\cdot,x)$ for $x\in\mathcal X$, compactness of $\mathcal X$) and Assumption 3 (Slater), there exists a finitely atomic PSD matrix-valued measure $\Phi^\star=\sum_{i=1}^r W_i\delta_{x^{(i)}}$ on $\mathcal X$ such that
--   $$f^\star=\inf_{y\in\mathcal Y}\ f(y)-\mathscr L_{\Phi^\star}(P(y,x)),\qquad \mathscr L_{\Phi^\star}(P(y,x))=\sum_{i=1}^r\operatorname{tr}\big(P(y,x^{(i)})W_i\big).$$
--   Moreover, $\mathscr L_{\Phi^\star}(P(y^\star,x))=0$ for every optimal solution $y^\star$ of (RPMIO).
--
--   The measure $\Phi^\star$ is a Lagrange multiplier for the infinitely many matrix constraints: it reduces the robust problem to a convex problem over $\mathcal Y$ alone. It is the starting point of the lower bound $f^\star\le f^{\mathrm{primal}}_k$.
--
--   **Formalization Note** The infimum is stated as "$f^\star$ is the greatest lower bound of $\{f(y)-\mathscr L_{\Phi^\star}(P(y,x)):y\in\mathcal Y\}$", so no junk value of a real infimum of an unbounded set can enter. The standing assumption of p. 2 (an optimizer exists) and the symmetry of $P$ and $G$ are hypotheses.
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 17, Proposition 4.1

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model

namespace RobustPMI.Hierarchy

open MvPolynomial

/-- Proposition 4.1 (p. 17): under Assumptions 1 and 3 (and the standing assumption that (RPMIO) has
an optimizer), there is a finitely atomic PSD matrix-valued measure `Φ⋆` on `𝒳` with
`f⋆ = inf_{y ∈ 𝒴} f(y) − 𝓛_{Φ⋆}(P(y, x))`, and `𝓛_{Φ⋆}(P(y⋆, x)) = 0` at every optimal `y⋆`. -/
theorem proposition_4_1 {ℓ n m q s : ℕ} (f : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP : P.IsSymm) (hG : G.IsSymm)
    (h1 : Assumption1 f θ P G) (h3 : Assumption3 θ P G)
    (hmin : ∃ y, IsGlobalMin f θ P G y) :
    ∃ μ : AtomicMeasure m G,
      IsGLB ((fun y => eval y f - μ.rieszP P y) '' Yset θ) (fstar f θ P G) ∧
      ∀ y, IsGlobalMin f θ P G y → μ.rieszP P y = 0 := by sorry

end RobustPMI.Hierarchy
