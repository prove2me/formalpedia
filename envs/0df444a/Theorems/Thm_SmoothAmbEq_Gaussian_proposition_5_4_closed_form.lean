-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_proposition_5_4_closed_form
-- name    : SmoothAmbEq.Gaussian.proposition_5_4_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:22.161771+00:00
-- url     : https://prove2.me/theorems/67478304-9d97-43b6-96d5-ba87d5b8bf39
-- title:
--   Proposition 5.4, pp. 17–18 — closed-form solution of (5.16): (a) α = 0, (b) α = 1, (c) α ∉ {0, 1} through Ψ
-- statement:
--   Let $\alpha>\alpha^*$ and let $(m_2,m_3)$ solve (5.16) on $[0,T]$. Then for every $t\in[0,T]$:
--
--   1. if $\alpha=0$,
--   $$m_2(t)=\frac{\zeta(t)^{-1}}{1+\log\frac{\zeta(t)}{\zeta(T)}}-\zeta(t)^{-1},\qquad m_3(t)=\zeta(T)^{-1}\int_0^{\log\frac{\zeta(t)}{\zeta(T)}}e^{-x}(1+x)^{-2}dx-\frac{T-t}{\sigma^2};$$
--   2. if $\alpha=1$,
--   $$m_2(t)=\frac{\zeta(t)^{-1}}{1+\sigma^{-2}\zeta(T)(T-t)}-\zeta(t)^{-1},\qquad m_3(t)=\zeta(t)^{-1}-\frac{\zeta(T)^{-1}}{1+\sigma^{-2}\zeta(T)(T-t)};$$
--   3. if $\alpha\notin\{0,1\}$, then $m_2(t)=-\zeta(t)^{-1}\Psi^{-1}\big(\sigma^{-2}\zeta(T)(T-t)\big)$, that is, $x(t):=-\zeta(t)m_2(t)$ lies in $[0,1/(\alpha\vee1))$ and $\Psi(x(t))=\sigma^{-2}\zeta(T)(T-t)$, and
--   $$m_3(t)=\frac1\alpha\Big(\zeta(t)^{-1}-\zeta(T)^{-1}e^{\frac{\zeta(t)m_2(t)}{1+\zeta(t)m_2(t)}}\big[1+\zeta(t)m_2(t)\big]^{\frac{\alpha}{\alpha-1}}\big[1+\alpha\zeta(t)m_2(t)\big]^{-\frac{1}{\alpha-1}}\Big),$$
--   where $\Psi(x)=\int_0^x\frac{ds}{\psi(s)}$ and $\psi(x)=e^{\frac{x}{1-x}}(1-x)^{\frac{\alpha-2}{\alpha-1}}(1-\alpha x)^{\frac{\alpha}{\alpha-1}}$.
--
--   These formulas make the equilibrium strategy (5.12) explicit.
--
--   **Formalization Note** In case 3 the inverse $\Psi^{-1}$ is not written as a function: the statement says that $x(t)$ is in the domain $[0,1/(\alpha\vee1))$ and solves $\Psi(x(t))=\sigma^{-2}\zeta(T)(T-t)$. Since $\psi>0$ there, $\Psi$ is strictly increasing and this determines $x(t)$, so no default value of an inverse enters. All real powers have positive bases on the stated ranges.
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, pp. 17–18, Proposition 5.4 (a)–(c)

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory Set

namespace SmoothAmbEq.Gaussian

/-- Proposition 5.4, pp. 17–18: for `α > α*` the solution of (5.16) is given in closed form,
(a) for `α = 0`, (b) for `α = 1`, (c) for `α ∈ (α*, ∞) \ {0, 1}`; in case (c),
`m₂(t) = -ζ(t)⁻¹Ψ⁻¹(σ⁻²ζ(T)(T - t))` is written as: `x(t) := -ζ(t)m₂(t) ∈ [0, 1/(α ∨ 1))`
and `Ψ(x(t)) = σ⁻²ζ(T)(T - t)` (`Ψ` is strictly increasing there). -/
theorem proposition_5_4_closed_form (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : a < M.α) (m₂ m₃ : ℝ → ℝ) (h : SolvesODE516 M m₂ m₃) :
    (M.α = 0 → ∀ t ∈ Icc 0 M.T,
      m₂ t = (M.ζ t)⁻¹ / (1 + Real.log (M.ζ t / M.ζ M.T)) - (M.ζ t)⁻¹ ∧
      m₃ t = (M.ζ M.T)⁻¹ * (∫ x in (0 : ℝ)..Real.log (M.ζ t / M.ζ M.T),
          Real.exp (-x) * ((1 + x) ^ 2)⁻¹) - (M.T - t) / M.σ ^ 2) ∧
    (M.α = 1 → ∀ t ∈ Icc 0 M.T,
      m₂ t = (M.ζ t)⁻¹ / (1 + (M.σ ^ 2)⁻¹ * M.ζ M.T * (M.T - t)) - (M.ζ t)⁻¹ ∧
      m₃ t = (M.ζ t)⁻¹ - (M.ζ M.T)⁻¹ / (1 + (M.σ ^ 2)⁻¹ * M.ζ M.T * (M.T - t))) ∧
    (M.α ≠ 0 → M.α ≠ 1 → ∀ t ∈ Icc 0 M.T,
      -(M.ζ t * m₂ t) ∈ Ico 0 (1 / max M.α 1) ∧
      Ψ M (-(M.ζ t * m₂ t)) = (M.σ ^ 2)⁻¹ * M.ζ M.T * (M.T - t) ∧
      m₃ t = 1 / M.α * ((M.ζ t)⁻¹ - (M.ζ M.T)⁻¹
        * Real.exp (M.ζ t * m₂ t / (1 + M.ζ t * m₂ t))
        * (1 + M.ζ t * m₂ t) ^ (M.α / (M.α - 1))
        * (1 + M.α * M.ζ t * m₂ t) ^ (-1 / (M.α - 1)))) := by sorry

end SmoothAmbEq.Gaussian
