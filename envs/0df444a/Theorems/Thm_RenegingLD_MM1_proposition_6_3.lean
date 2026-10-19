-- Prove2me | Theorems.Thm_RenegingLD_MM1_proposition_6_3
-- name    : RenegingLD.MM1.proposition_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:24.820969+00:00
-- url     : https://prove2.me/theorems/6c0a5ef5-5c9a-4bd8-8d5d-5bf9a7994b5c
-- title:
--   Proposition 6.3, p. 32 — lower bound lim inf_{T→∞} I*_{γ,T}/T ≥ C(γ) for every γ > 0
-- statement:
--   Let $\lambda\ge\mu>0$, $\theta>0$, $x_0\ge0$ and fix $\gamma>0$. Then
--   $$\liminf_{T\to\infty}\frac{I^*_{\gamma,T}}{T}\ge C(\gamma).$$
--
--   Together with Proposition 6.2 this gives $I^*_{\gamma,T}/T\to C(\gamma)$ for $\gamma>0$ and every $x_0\ge0$, including $x_0=0$, where the explicit minimizer of Lemma 5.7 is not available.
--
--   **Formalization Note.** The ratio is computed in $[0,\infty]$, where `liminf` is never a junk value.
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 32, Proposition 6.3

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

theorem proposition_6_3 (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (x0 γ : ℝ) (hx0 : 0 ≤ x0) (hγ : 0 < γ) :
    ENNReal.ofReal (C lam mu γ) ≤
      Filter.liminf (fun T => Istar lam mu θ x0 γ T / ENNReal.ofReal T) atTop := by sorry

end RenegingLD.MM1
