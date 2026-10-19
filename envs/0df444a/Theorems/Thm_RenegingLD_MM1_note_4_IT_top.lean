-- Prove2me | Theorems.Thm_RenegingLD_MM1_note_4_IT_top
-- name    : RenegingLD.MM1.note_4_IT_top
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:03.871483+00:00
-- url     : https://prove2.me/theorems/3521dc69-ea16-4f1d-bae3-f6e62a3618c0
-- title:
--   §4, p. 18 — the rate function I_T(ξ, ζ) is infinite for (ξ, ζ) ∉ C_T
-- statement:
--   Let $\lambda\ge\mu>0$, $\theta>0$, $x_0\ge0$ and $T>0$, and let $\mathcal C_T$ be the class of continuous nonnegative paths $(\xi,\zeta)$ on $[0,T]$ with $\xi(0)=x_0$, $\zeta(0)=0$, both absolutely continuous, $\zeta'=0$ a.e. on $\{\xi=0\}$ and $\zeta$ nondecreasing. Then for every pair $(\xi,\zeta)$,
--   $$(\xi,\zeta)\notin\mathcal C_T\ \Longrightarrow\ I_T(\xi,\zeta)=\infty .$$
--
--   Equivalently, a path with a nonempty control set $\mathcal U(\xi,\zeta)$ lies in $\mathcal C_T$, so every variational problem for $I_T$ can be restricted to $\mathcal C_T$.
--
--   **Formalization Note.** `lam`, `mu` stand for $\lambda,\mu$. The standing assumptions of §4 ($\lambda\ge\mu$) and §2 ($\lambda,\mu,\theta>0$, $x_0\ge0$, $T>0$) are explicit hypotheses.
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 18, §4, 'We note that I_T(ξ, ζ) = ∞ if (ξ, ζ) ∉ C_T.'

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

theorem note_4_IT_top (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (x0 T : ℝ) (hx0 : 0 ≤ x0) (hT : 0 < T)
    (ξ ζ : ℝ → ℝ) (h : ¬ InCT x0 T ξ ζ) :
    IT lam mu θ x0 T ξ ζ = ⊤ := by sorry

end RenegingLD.MM1
