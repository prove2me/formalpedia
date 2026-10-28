-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_proposition_5_4_existence_uniqueness
-- name    : SmoothAmbEq.Gaussian.proposition_5_4_existence_uniqueness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:09.976799+00:00
-- url     : https://prove2.me/theorems/4da5167c-6e82-400d-af91-f6e5350190a5
-- title:
--   Proposition 5.4, p. 17 — for every α > α*, the system (5.16) has a unique solution on [0, T]
-- statement:
--   Let $\alpha^*$ be the critical exponent of (5.17) and $\alpha>\alpha^*$. Then the terminal-value problem
--   $$\sigma^2m_2'=(1+\zeta m_2)\,a_1(t,m_2,m_3)+\zeta m_2,\qquad\sigma^2m_3'=-2\zeta m_2-\zeta^2m_2^2,\qquad m_2(T)=m_3(T)=0\qquad(5.16)$$
--   has a solution on $[0,T]$, and any two solutions coincide on $[0,T]$.
--
--   (5.16) is the nonlinear core of the six-dimensional system (5.10); once it is solved, the remaining coefficients follow from linear equations, (5.18).
--
--   **Formalization Note** A solution keeps $\zeta(t)^{-1}-\alpha m_3(t)>0$ on $[0,T]$, the denominator of $a_1$; only there is (5.16) defined (Lean's $x/0=0$ would otherwise admit spurious solutions). Uniqueness is on $[0,T]$, the interval on which the system lives.
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, p. 17, Proposition 5.4, (5.16)

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory Set

namespace SmoothAmbEq.Gaussian

/-- Proposition 5.4, p. 17: for every `α > α*`, the system (5.16) has a unique solution on
`[0, T]` (among pairs keeping `ζ(t)⁻¹ - αm₃(t) > 0`, so that (5.16) is defined). -/
theorem proposition_5_4_existence_uniqueness (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : a < M.α) :
    (∃ m₂ m₃ : ℝ → ℝ, SolvesODE516 M m₂ m₃) ∧
    ∀ m₂ m₃ m₂' m₃' : ℝ → ℝ, SolvesODE516 M m₂ m₃ → SolvesODE516 M m₂' m₃' →
      EqOn m₂ m₂' (Icc 0 M.T) ∧ EqOn m₃ m₃' (Icc 0 M.T) := by sorry

end SmoothAmbEq.Gaussian
