-- Prove2me | Theorems.Thm_RenegingLD_MM1_proposition_6_4
-- name    : RenegingLD.MM1.proposition_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:34.707231+00:00
-- url     : https://prove2.me/theorems/eb065f48-0c72-4ab4-bf55-680bee326a69
-- title:
--   Proposition 6.4, p. 33 — lower bound lim inf_{T→∞} I*_{0,T}/T ≥ C(0)
-- statement:
--   Let $\lambda\ge\mu>0$, $\theta>0$ and $x_0\ge0$. Then
--   $$\liminf_{T\to\infty}\frac{I^*_{0,T}}{T}\ge C(0),$$
--   where $I^*_{0,T}$ is the cost of seeing no reneging at all on $[0,T]$ and $C(0)=\lambda+\mu-2\sqrt{\lambda\mu}$.
--
--   This completes the lower bound of Theorem 2.3 at $\gamma=0$.
--
--   **Formalization Note.** The ratio is computed in $[0,\infty]$. The statement includes $\lambda=\mu$, where $C(0)=0$ and it is trivially true.
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 33, Proposition 6.4

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

theorem proposition_6_4 (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (x0 : ℝ) (hx0 : 0 ≤ x0) :
    ENNReal.ofReal (C lam mu 0) ≤
      Filter.liminf (fun T => Istar lam mu θ x0 0 T / ENNReal.ofReal T) atTop := by sorry

end RenegingLD.MM1
