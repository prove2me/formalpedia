-- Prove2me | Theorems.Thm_RenegingLD_MM1_lemma_4_1
-- name    : RenegingLD.MM1.lemma_4_1
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:10.909523+00:00
-- url     : https://prove2.me/theorems/3bebfec4-417e-49d0-b238-6a2085396fc1
-- title:
--   Lemma 4.1, p. 19 — on C_T the rate function is the integral of the local rate L(ξ, ξ′, ζ′)
-- statement:
--   Let $\lambda\ge\mu>0$, $\theta>0$, $x_0\ge0$, $T>0$, and let $L$ be the local rate of §4. For every $(\xi,\zeta)\in\mathcal C_T$,
--   $$I_T(\xi,\zeta)=\int_0^T L\big(\xi(s),\xi'(s),\zeta'(s)\big)\,ds. \tag{4.1}$$
--
--   This replaces the infimum over controls in (2.6) by an explicit integral functional of the path and its derivative, which is the form used in the Euler–Lagrange analysis of §5.
--
--   **Formalization Note.** $\xi',\zeta'$ are Lean's `deriv` (the a.e. derivatives of the absolutely continuous paths); the integral is a lower Lebesgue integral in $[0,\infty]$, so both sides may equal $\infty$. Standing assumptions are explicit hypotheses.
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 19, Lemma 4.1, (4.1)

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

theorem lemma_4_1 (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (x0 T : ℝ) (hx0 : 0 ≤ x0) (hT : 0 < T)
    (ξ ζ : ℝ → ℝ) (h : InCT x0 T ξ ζ) :
    IT lam mu θ x0 T ξ ζ =
      ∫⁻ s in Set.Icc 0 T, Lloc lam mu θ (ξ s) (deriv ξ s) (deriv ζ s) := by sorry

end RenegingLD.MM1
