-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_proposition_5_4_existence
-- name    : SmoothAmbEq.Gaussian.proposition_5_4_existence
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T19:23:07.06157+00:00
-- url     : https://prove2.me/theorems/a10d11c9-1a9d-4511-98b4-1613c4519e6b
-- title:
--   Proposition 5.4, p. 17 — for every α > α*, (5.16) has a solution on [0, T]
-- statement:
--   Let $\alpha^*<0$ be the critical exponent of Proposition 5.4, i.e. the unique $\alpha^*<0$ with
--   $$(1+\sigma_0^{-2}\sigma^2T^{-1})\int_0^\infty e^{-x}\big(1+(1-\alpha^*)x\big)^{\alpha^*/(1-\alpha^*)}dx=1 .\qquad(5.17)$$
--   If $\alpha>\alpha^*$, then the terminal-value problem (5.16)
--   $$\sigma^2m_2'(t)=\big(1+\zeta(t)m_2(t)\big)a_1\big(t,m_2(t),m_3(t)\big)+\zeta(t)m_2(t),\qquad \sigma^2m_3'(t)=-2\zeta(t)m_2(t)-\zeta(t)^2m_2(t)^2,$$
--   $m_2(T)=m_3(T)=0$, has a solution $(m_2,m_3)$ on $[0,T]$ with $\zeta(t)^{-1}-\alpha m_3(t)>0$ for all $t\in[0,T]$, where $\zeta(t)=\sigma^2\sigma_0^2/(\sigma^2+t\sigma_0^2)$ and $a_1(t,m_2,m_3)=(1+\zeta m_2)(\zeta^{-1}+\alpha m_2)/(\zeta^{-1}-\alpha m_3)$.
--
--   This is the existence half of the second assertion of Proposition 5.4 ("for every $\alpha>\alpha^*$, (5.16) has a unique solution"); uniqueness follows from the closed form of the solution. In the paper the solution is constructed explicitly: for $\alpha\notin\{0,1\}$, $\zeta m_2=-\Psi^{-1}(\sigma^{-2}\zeta(T)(T-t))$, which is well defined exactly when $\alpha>\alpha^*$.
--
--   **Formalization Note.** Derivatives are one-sided at the endpoints (`HasDerivWithinAt` on $[0,T]$), as in the predicate `SolvesODE516`.
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, p. 17, Proposition 5.4 (existence part of 'for every α > α*, (5.16) has a unique solution'); proof in the appendix 'Proof of Proposition 5.4'

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory Set

namespace SmoothAmbEq.Gaussian

/-- Proposition 5.4, p. 17 (existence part): for every `α > α*`, the system (5.16) has a
solution on `[0, T]` (keeping `ζ(t)⁻¹ - αm₃(t) > 0`). -/
theorem proposition_5_4_existence (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : a < M.α) : ∃ m₂ m₃ : ℝ → ℝ, SolvesODE516 M m₂ m₃ := by sorry

end SmoothAmbEq.Gaussian
