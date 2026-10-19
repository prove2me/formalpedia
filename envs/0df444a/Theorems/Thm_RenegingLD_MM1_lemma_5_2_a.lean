-- Prove2me | Theorems.Thm_RenegingLD_MM1_lemma_5_2_a
-- name    : RenegingLD.MM1.lemma_5_2_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:14.46298+00:00
-- url     : https://prove2.me/theorems/52914ad9-5592-4882-b28e-daf16772ab5f
-- title:
--   Lemma 5.2(a), p. 23 — for γ > 0 equation (5.9) has a unique root A ∈ (−∞, e^{−θT})
-- statement:
--   Let $\lambda\ge\mu>0$, $\theta>0$, $x_0\ge0$, $T>0$ and $\gamma>0$. There is exactly one $A\in(-\infty,e^{-\theta T})$ satisfying equation (5.9),
--   $$\frac{1}{1-Ae^{\theta T}}=\frac{\theta[\gamma T-x_0+x_0\Lambda(A,T)]+\Big(\theta^2[\gamma T-x_0+x_0\Lambda(A,T)]^2-4\lambda[\theta T-1+e^{-\theta T}]\mu[\log\Lambda(A,T)-\Lambda(A,T)+1]\Big)^{1/2}}{2\lambda[\theta T-1+e^{-\theta T}]},$$
--   where $\Lambda(A,T)=(e^{-\theta T}-A)/(1-A)$.
--
--   The root determines the constants $(A,B)$, $B=1/(1-Ae^{\theta T})$, of the explicit candidate minimizer (Construction 5.3).
--
--   **Formalization Note.** Standing assumptions are explicit hypotheses. Uniqueness is stated with `∃!`.
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 23, Lemma 5.2(a), (5.9)

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

theorem lemma_5_2_a (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (γ x0 T : ℝ) (hγ : 0 < γ) (hx0 : 0 ≤ x0) (hT : 0 < T) :
    ∃! A : ℝ, A < Real.exp (-θ * T) ∧ eq59 lam mu θ γ x0 T A := by sorry

end RenegingLD.MM1
