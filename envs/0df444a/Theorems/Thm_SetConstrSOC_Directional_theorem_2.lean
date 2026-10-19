-- Prove2me | Theorems.Thm_SetConstrSOC_Directional_theorem_2
-- name    : SetConstrSOC.Directional.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:12.029453+00:00
-- url     : https://prove2.me/theorems/dc6d14f0-5cf7-48a0-8ec5-33fd61c4b9bc
-- title:
--   Theorem 2 — directional second-order necessary condition
-- statement:
--   Let $\bar x$ be a locally optimal feasible solution of (P). Suppose $g(x)-\Lambda$ is metrically subregular at $(\bar x,0)$ in a critical direction $d\in C(\bar x)$ and $D=T_\Lambda^2(g(\bar x);\nabla g(\bar x)d)$ is nonempty. Put $A_{\rm opt}=\nabla g(\bar x)T_F^2(\bar x;d)+\nabla^2g(\bar x)(d,d)$. There exists one directional M-multiplier $\lambda\in\Lambda(\bar x;d)$ such that, for every set $A\supseteq A_{\rm opt}$,
--
--   $$
--   \widehat\sigma_{D,A}(\lambda)\le\nabla^2_{xx}L(\bar x,\lambda)(d,d).
--   $$
--
--   The same multiplier satisfies $\widehat\sigma_D(\lambda)\le\nabla^2_{xx}L(\bar x,\lambda)(d,d)$. These are (17) and (18), respectively, with $L(x,\lambda)=f(x)+g(x)^\top\lambda$.
--
--   This is the paper's directional dual second-order necessary condition for a nonconvex constraint set.
--
--   **Formalization Note** The paper writes each inequality as a real Hessian minus a support value being nonnegative; order comparison in extended reals avoids subtraction at infinity. The single multiplier also gives (18) by taking $A=\mathbb R^m$.
-- source:
--   Gfrerer, Ye & Zhou, Second-order optimality conditions for non-convex set-constrained optimization problems, arXiv:1911.04076v2, p. 16, Theorem 2, (17)–(18)

import Mathlib
import Definitions.Def_SetConstrSOC_Directional_Model

namespace SetConstrSOC.Directional

/-- Theorem 2, p. 16, (17)–(18): a directional second-order necessary condition. -/
theorem theorem_2 {n m : ℕ} (P : Problem n m) (hP : P.Standing)
    (x d : E n) (hmin : IsLocalMinOn P.f P.feasible x) (hx : x ∈ P.feasible)
    (hMS : MetricSubregularDirAt P.g P.Λ x d) (hd : d ∈ P.criticalCone x)
    (hD : (secondOrderTangentSet P.Λ (P.g x) ((fderiv ℝ P.g x) d)).Nonempty) :
    ∃ lam ∈ P.dirMMultipliers x d,
      (∀ A : Set (E m),
        ((fun w => (fderiv ℝ P.g x) w + ((fderiv ℝ (fderiv ℝ P.g) x) d) d) ''
          secondOrderTangentSet P.feasible x d) ⊆ A →
        lowerGenSupport
          (secondOrderTangentSet P.Λ (P.g x) ((fderiv ℝ P.g x) d)) A lam ≤
          (P.hessLag x lam d : EReal)) ∧
      lowerGenSupport₀
        (secondOrderTangentSet P.Λ (P.g x) ((fderiv ℝ P.g x) d)) lam ≤
        (P.hessLag x lam d : EReal) := by sorry

end SetConstrSOC.Directional
