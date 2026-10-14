-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_eq_5_18
-- name    : SmoothAmbEq.Gaussian.eq_5_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:29.663237+00:00
-- url     : https://prove2.me/theorems/5f4b7177-ac9b-40c4-8c58-98a2756239b9
-- title:
--   (5.18), §5.3, p. 18 — the closed-form m₁, m₄, m₅, m₆ complete the solution of (5.16) to a solution of (5.10)
-- statement:
--   Let $\alpha>\alpha^*$, let $(m_2,m_3)$ solve (5.16) on $[0,T]$, and put $A_i(t)=a_i(t,m_2(t),m_3(t))$. Define
--   $$\begin{aligned}m_1(t)&=\sigma^{-2}\zeta(t)^{-2}\int_t^T\zeta^2(s)A_1^2(s)\,ds,\qquad m_4=-rm_1-rm_2,\qquad m_5=-rm_2-rm_3,\\ m_6(t)&=\sigma^{-2}\int_t^T\Big[\tfrac12A_2^2(s)m_5^2(s)-\tfrac12r^2+\tfrac12\zeta^2(s)m_1(s)+r\zeta(s)m_4(s)\Big]ds.\end{aligned}\qquad(5.18)$$
--   Then $(m_1,\dots,m_6)$ solves the full system (5.10) on $[0,T]$.
--
--   Together with Proposition 5.4 this shows that the coefficients assumed in Theorem 5.5 exist.
--
--   **Formalization Note** The conclusion is the solution predicate of (5.10), which includes $\zeta(t)^{-1}-\alpha m_3(t)>0$ on $[0,T]$ (already part of the hypothesis on $(m_2,m_3)$).
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, p. 18, §5.3, (5.18)

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory Set

namespace SmoothAmbEq.Gaussian

/-- (5.18), §5.3, p. 18: for `α > α*` and `(m₂, m₃)` the solution of (5.16), the functions
`m₁, m₄, m₅, m₆` given in closed form by (5.18) complete `(m₂, m₃)` to a solution of the full
system (5.10). -/
theorem eq_5_18 (M : Model) (a : ℝ) (ha : IsAlphaStar M a) (hα : a < M.α)
    (m₂ m₃ : ℝ → ℝ) (h : SolvesODE516 M m₂ m₃) :
    SolvesODE510 M (coeffs518 M m₂ m₃) := by sorry

end SmoothAmbEq.Gaussian
