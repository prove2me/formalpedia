-- Prove2me | Theorems.Thm_RenegingLD_MM1_lemma_5_5_a
-- name    : RenegingLD.MM1.lemma_5_5_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:18.36157+00:00
-- url     : https://prove2.me/theorems/93652626-6ddc-435a-ac36-ac9ffd808ed2
-- title:
--   Lemma 5.5(a), p. 26 — for large T the candidate ξ̄ is positive on (0, T] and (ξ̄, ζ̄) ∈ C_T
-- statement:
--   Let $\lambda\ge\mu>0$, $\theta>0$, $\gamma>0$, and let $K\subset\mathbb R_+$ be compact. There is $T_0\in(0,\infty)$ such that for every $T\ge T_0$ and every $x_0\in K$ the following holds. If $A<e^{-\theta T}$ satisfies (5.9), $B=1/(1-Ae^{\theta T})$, and $(\bar\xi,\bar\zeta)$ are given by (5.3)–(5.4) (Construction 5.3), then
--   $$\bar\xi(t)>0\ \text{ for all } t\in(0,T]\qquad\text{and}\qquad(\bar\xi,\bar\zeta)\in\mathcal C_T .$$
--
--   This makes the candidate a legitimate competitor in the variational problem for $I^*_{\gamma,T}$.
--
--   **Formalization Note.** $T_0$ depends on $K$ and $\gamma$ but not on $x_0\in K$, as on the page. The root of (5.9) is quantified, not chosen.
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 26, Lemma 5.5(a)

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

theorem lemma_5_5_a (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (γ : ℝ) (hγ : 0 < γ)
    (K : Set ℝ) (hK : IsCompact K) (hK0 : K ⊆ Set.Ici 0) :
    ∃ T0 : ℝ, 0 < T0 ∧ ∀ T : ℝ, T0 ≤ T → ∀ x0 ∈ K, ∀ A B : ℝ,
      A < Real.exp (-θ * T) → eq59 lam mu θ γ x0 T A →
      B = 1 / (1 - A * Real.exp (θ * T)) →
        (∀ t ∈ Set.Ioc 0 T, 0 < xiBar lam mu θ x0 A B t) ∧
        InCT x0 T (fun t => xiBar lam mu θ x0 A B t) (fun t => zetaBar lam mu θ x0 A B t) := by sorry

end RenegingLD.MM1
