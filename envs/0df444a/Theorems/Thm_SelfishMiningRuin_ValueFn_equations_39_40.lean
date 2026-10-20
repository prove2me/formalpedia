-- Prove2me | Theorems.Thm_SelfishMiningRuin_ValueFn_equations_39_40
-- name    : SelfishMiningRuin.ValueFn.equations_39_40
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:10.031386+00:00
-- url     : https://prove2.me/theorems/17d44551-5241-4e20-b701-1fcf44214f64
-- title:
--   Equations (39)–(40), p. 28, with corrected (23) — explicit candidate and boundary conditions
-- statement:
--   Let $\rho_1$ be a real root and $\rho_2+i\rho_3$ a complex root of characteristic equation (35). For real coefficients $A_1,A_2,A_3$, let
--
--   $$
--   F(u)=A_1e^{\rho_1u}+e^{\rho_2u}\bigl(A_2\cos(\rho_3u)+A_3\sin(\rho_3u)\bigr)+u+C.
--   $$
--
--   This function solves the inhomogeneous advanced equation (32) at every real $u$. Its three boundary conditions (33), namely $F(0)=F'(0)=0$ and $F''(0)=(\lambda^2p^2/c^2)F(2b)+1/(ct)$, hold exactly when $(A_1,A_2,A_3)$ solves the corrected linear system (23).
--
--   This result characterizes the explicit candidate used in the main theorem.
--
--   **Formalization Note** The third right-hand side of printed (23) omits $\lambda^2p^2/c^2$ on $2b+C$. Equation (40)'s $bu$ is read as $Bu$ with the particular-solution coefficient $B=1$, consistent with (20). The page's further remark that (39) with the particular solution gives "the generic solutions" of (32) is not stated: (32) has further exponential solutions for roots of (35) with positive real part, and restricting to linear growth is the uniqueness the paper assumes on p. 25.
-- source:
--   Albrecher & Goffard, On the profitability of selfish blockchain mining under consideration of ruin, arXiv:2010.12577v1, p. 28, equations (39), (40); p. 11, corrected equation (23); p. 25, equations (32), (33)

import Mathlib
import Definitions.Def_SelfishMiningRuin_ValueFn_Formula

set_option autoImplicit false

namespace SelfishMiningRuin.ValueFn

/-- Equations (39)–(40), p. 28, with (23), p. 11, corrected: the third right-hand side of (23) needs the factor λ²p²/c² on 2b+C. -/
theorem equations_39_40 (lam c b t p q rho1 rho2 rho3 A1 A2 A3 : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (hb : 0 < b) (ht : 0 < t)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hroot1 : charFun lam c b t p q (rho1 : ℂ) = 0)
    (hroot2 : charFun lam c b t p q (Complex.mk rho2 rho3) = 0) :
    let F := closedForm lam c b t p q rho1 rho2 rho3 A1 A2 A3
    (∀ u : ℝ, E32 lam c b t p q F u = 0) ∧
    ((F 0 = 0 ∧ deriv F 0 = 0 ∧
      iteratedDeriv 2 F 0 = lam^2*p^2/c^2*F (2*b) + 1/(c*t)) ↔
      System23 lam c b t p q rho1 rho2 rho3 A1 A2 A3) := by sorry

end SelfishMiningRuin.ValueFn
