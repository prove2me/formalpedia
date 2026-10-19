-- Prove2me | Theorems.Thm_RenegingLD_MM1_lemma_5_5_b
-- name    : RenegingLD.MM1.lemma_5_5_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:26.306604+00:00
-- url     : https://prove2.me/theorems/b9ddc41c-f689-409f-9235-86a247caabcb
-- title:
--   Lemma 5.5(b), p. 26 — for x₀ > 0, two-sided bounds on ξ̄ and ζ̄′ and a bound on |ξ̄′|
-- statement:
--   Let $\lambda\ge\mu>0$, $\theta>0$, $\gamma>0$, and let $K\subset\mathbb R_+$ be compact. There is $T_0\in(0,\infty)$ such that for every $T\ge T_0$ and every $x_0\in K\setminus\{0\}$ the following holds. If $A<e^{-\theta T}$ satisfies (5.9), $B=1/(1-Ae^{\theta T})$ and $(\bar\xi,\bar\zeta)$ is the candidate of Construction 5.3, then there is $c_0\in(0,\infty)$ with
--   $$c_0^{-1}\le\bar\xi(t)\le c_0,\qquad|\bar\xi'(t)|\le c_0,\qquad c_0^{-1}\le\bar\zeta'(t)\le c_0\qquad\text{for all }t\in[0,T].$$
--
--   These bounds justify differentiating under the integral sign in the first-variation argument of Lemma 5.7.
--
--   **Formalization Note.** As on the page, $c_0$ may depend on $T$ and $x_0$ (it is chosen after them); $T_0$ depends only on $K$ and $\gamma$. Derivatives are `deriv` of the explicit smooth formulas (5.3)–(5.4).
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 26, Lemma 5.5(b)

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

theorem lemma_5_5_b (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (γ : ℝ) (hγ : 0 < γ)
    (K : Set ℝ) (hK : IsCompact K) (hK0 : K ⊆ Set.Ici 0) :
    ∃ T0 : ℝ, 0 < T0 ∧ ∀ T : ℝ, T0 ≤ T → ∀ x0 ∈ K, x0 ≠ 0 → ∀ A B : ℝ,
      A < Real.exp (-θ * T) → eq59 lam mu θ γ x0 T A →
      B = 1 / (1 - A * Real.exp (θ * T)) →
        ∃ c0 : ℝ, 0 < c0 ∧ ∀ t ∈ Set.Icc 0 T,
          c0⁻¹ ≤ xiBar lam mu θ x0 A B t ∧ xiBar lam mu θ x0 A B t ≤ c0 ∧
          |deriv (fun s => xiBar lam mu θ x0 A B s) t| ≤ c0 ∧
          c0⁻¹ ≤ deriv (fun s => zetaBar lam mu θ x0 A B s) t ∧
          deriv (fun s => zetaBar lam mu θ x0 A B s) t ≤ c0 := by sorry

end RenegingLD.MM1
