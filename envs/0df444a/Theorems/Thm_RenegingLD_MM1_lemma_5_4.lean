-- Prove2me | Theorems.Thm_RenegingLD_MM1_lemma_5_4
-- name    : RenegingLD.MM1.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:21.878968+00:00
-- url     : https://prove2.me/theorems/a55ece03-1106-4941-8cdd-ba8f910fb0d3
-- title:
--   Lemma 5.4, p. 25 — the candidate meets the terminal condition ζ̄(T) = γT
-- statement:
--   Let $\lambda\ge\mu>0$, $\theta>0$, $x_0\ge0$, $T>0$ and $\gamma>0$. Let $A<e^{-\theta T}$ satisfy (5.9), let $B=1/(1-Ae^{\theta T})$ and let $\bar\zeta$ be given by (5.4) with these constants (Construction 5.3). Then
--   $$\bar\zeta(T)=\gamma T .$$
--
--   So the candidate of Construction 5.3 is admissible for the variational problem defining $I^*_{\gamma,T}$.
--
--   **Formalization Note.** Standing assumptions are explicit hypotheses; the root of (5.9) is quantified, not chosen.
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 25, Lemma 5.4 (Construction 5.3, p. 25; (5.4), (5.9), p. 23)

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

theorem lemma_5_4 (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (γ x0 T : ℝ) (hγ : 0 < γ) (hx0 : 0 ≤ x0) (hT : 0 < T)
    (A B : ℝ) (hA : A < Real.exp (-θ * T)) (h59 : eq59 lam mu θ γ x0 T A)
    (hB : B = 1 / (1 - A * Real.exp (θ * T))) :
    zetaBar lam mu θ x0 A B T = γ * T := by sorry

end RenegingLD.MM1
