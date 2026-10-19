-- Prove2me | Theorems.Thm_RenegingLD_MM1_lemma_5_7
-- name    : RenegingLD.MM1.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:23.654644+00:00
-- url     : https://prove2.me/theorems/b417b673-43d1-471f-8fa6-2360417f8e26
-- title:
--   Lemma 5.7, p. 28 — for x₀ > 0 and large T the candidate (ξ̄, ζ̄) attains I*_{γ,T}
-- statement:
--   Let $\lambda\ge\mu>0$, $\theta>0$, $\gamma>0$, and let $K\subset\mathbb R_+$ be compact. There is $T_1\in(0,\infty)$ such that for all $T\ge T_1$ and all $x_0\in K\setminus\{0\}$: if $A<e^{-\theta T}$ satisfies (5.9), $B=1/(1-Ae^{\theta T})$ and $(\bar\xi,\bar\zeta)$ is the candidate of Construction 5.3, then
--   $$I^*_{\gamma,T}=I_T(\bar\xi,\bar\zeta).$$
--
--   This identifies the explicit minimizer of the reneging variational problem for positive initial condition and long horizons.
--
--   **Formalization Note.** $T_1$ depends on $K$ and $\gamma$ only. The root of (5.9) is quantified, not chosen.
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 28, Lemma 5.7

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

theorem lemma_5_7 (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (γ : ℝ) (hγ : 0 < γ)
    (K : Set ℝ) (hK : IsCompact K) (hK0 : K ⊆ Set.Ici 0) :
    ∃ T1 : ℝ, 0 < T1 ∧ ∀ T : ℝ, T1 ≤ T → ∀ x0 ∈ K, x0 ≠ 0 → ∀ A B : ℝ,
      A < Real.exp (-θ * T) → eq59 lam mu θ γ x0 T A →
      B = 1 / (1 - A * Real.exp (θ * T)) →
        Istar lam mu θ x0 γ T =
          IT lam mu θ x0 T (fun t => xiBar lam mu θ x0 A B t)
            (fun t => zetaBar lam mu θ x0 A B t) := by sorry

end RenegingLD.MM1
