-- Prove2me | Theorems.Thm_RenegingLD_MM1_proposition_6_2
-- name    : RenegingLD.MM1.proposition_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:31.565255+00:00
-- url     : https://prove2.me/theorems/b69b42b1-6970-4fe0-a509-5be04e980c62
-- title:
--   Proposition 6.2, p. 31 — upper bound lim sup_{T→∞} I*_{γ,T}/T ≤ C(γ) for every γ ≥ 0
-- statement:
--   Let $\lambda\ge\mu>0$, $\theta>0$, $x_0\ge0$ and fix $\gamma\ge0$. Then
--   $$\limsup_{T\to\infty}\frac{I^*_{\gamma,T}}{T}\le C(\gamma).$$
--
--   This is the upper half of the first formula of Theorem 2.3.
--
--   **Formalization Note.** The ratio is computed in $[0,\infty]$, where `limsup` is never a junk value; $C(\gamma)\ge0$, so its embedding into $[0,\infty]$ loses nothing.
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 31, Proposition 6.2

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

theorem proposition_6_2 (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (x0 γ : ℝ) (hx0 : 0 ≤ x0) (hγ : 0 ≤ γ) :
    Filter.limsup (fun T => Istar lam mu θ x0 γ T / ENNReal.ofReal T) atTop ≤
      ENNReal.ofReal (C lam mu γ) := by sorry

end RenegingLD.MM1
