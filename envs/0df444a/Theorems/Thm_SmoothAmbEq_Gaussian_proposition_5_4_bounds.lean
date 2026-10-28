-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_proposition_5_4_bounds
-- name    : SmoothAmbEq.Gaussian.proposition_5_4_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:21.916717+00:00
-- url     : https://prove2.me/theorems/45a1e684-6415-4e88-8cc2-d7e5d1f8582d
-- title:
--   Proposition 5.4, p. 18 (Moreover) — 0 > ζm₂ > −1/(α∨1), m₃ < 0, ζ⁻¹ − αm₃ > 0 on [0, T)
-- statement:
--   Let $\alpha>\alpha^*$ and let $(m_2,m_3)$ solve (5.16). Then for every $t\in[0,T)$,
--   $$0>\zeta(t)m_2(t)>-\frac{1}{\alpha\vee1},\qquad m_3(t)<0,\qquad\zeta(t)^{-1}-\alpha m_3(t)>0.$$
--
--   These bounds keep every real power in the closed form positive-based and make $a_1,a_2$ bounded on $[0,T]$; the sign $m_3<0$ is what controls the growth of $g^z$ in the unobserved drift $z$.
--
--   **Formalization Note** The solution notion of (5.16) already includes $\zeta(t)^{-1}-\alpha m_3(t)>0$ on $[0,T]$ (see the Candidate definition), so the third bound is part of the hypothesis; the content of this item is the first two.
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, p. 18, Proposition 5.4 (Moreover)

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory Set

namespace SmoothAmbEq.Gaussian

/-- Proposition 5.4, p. 18 ("Moreover"): for `α > α*` the solution of (5.16) satisfies, for
every `t ∈ [0, T)`, `0 > ζ(t)m₂(t) > -1/(α ∨ 1)`, `m₃(t) < 0` and `ζ(t)⁻¹ - αm₃(t) > 0`. -/
theorem proposition_5_4_bounds (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : a < M.α) (m₂ m₃ : ℝ → ℝ) (h : SolvesODE516 M m₂ m₃) :
    ∀ t ∈ Ico 0 M.T,
      0 > M.ζ t * m₂ t ∧ M.ζ t * m₂ t > -(1 / max M.α 1) ∧ m₃ t < 0 ∧
      (M.ζ t)⁻¹ - M.α * m₃ t > 0 := by sorry

end SmoothAmbEq.Gaussian
