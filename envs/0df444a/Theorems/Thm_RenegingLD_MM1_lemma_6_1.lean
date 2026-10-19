-- Prove2me | Theorems.Thm_RenegingLD_MM1_lemma_6_1
-- name    : RenegingLD.MM1.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:27.687948+00:00
-- url     : https://prove2.me/theorems/f86f4878-e2ae-429a-b43f-4aa628c8ed5a
-- title:
--   Lemma 6.1, p. 30 — γ ↦ I*_{γ,T} is convex on [0, ∞), vanishes at γ*_T, decreases before it and increases after
-- statement:
--   Let $\lambda\ge\mu>0$, $\theta>0$, $x_0\ge0$ and $T>0$, and let
--   $$\gamma^*_T=(\lambda-\mu)+\frac{1-e^{-\theta T}}{T}\Big(x_0-\frac{\lambda-\mu}{\theta}\Big).$$
--   Then the map $\gamma\mapsto I^*_{\gamma,T}$ is a nonnegative convex function on $[0,\infty)$:
--   $$I^*_{a\gamma_1+(1-a)\gamma_2,T}\le a\,I^*_{\gamma_1,T}+(1-a)\,I^*_{\gamma_2,T}\qquad(\gamma_1,\gamma_2\ge0,\ a\in(0,1)),$$
--   it vanishes at $\gamma^*_T$, $I^*_{\gamma^*_T,T}=0$, and it is (weakly) decreasing on $[0,\gamma^*_T]$ and (weakly) increasing on $[\gamma^*_T,\infty)$.
--
--   $\gamma^*_T T$ is the reneging of the law-of-large-numbers path, which has zero cost; the shape of $\gamma\mapsto I^*_{\gamma,T}$ is used to pass from $I^*$ to the one-sided problems $I_{\gamma,T}$ and $\tilde I_{\gamma,T}$ in Theorem 2.3.
--
--   **Formalization Note.** Nonnegativity is automatic since $I^*$ takes values in $[0,\infty]$. "Decreasing/increasing" are read as nonstrict (`AntitoneOn`/`MonotoneOn`), which is what the proof ("immediate from convexity and nonnegativity") gives. $\gamma^*_T\ge0$ under the hypotheses, so the interval $[0,\gamma^*_T]$ is nonempty.
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 30, Lemma 6.1

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

theorem lemma_6_1 (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (x0 T : ℝ) (hx0 : 0 ≤ x0) (hT : 0 < T) :
    (∀ γ₁ γ₂ : ℝ, 0 ≤ γ₁ → 0 ≤ γ₂ → ∀ a ∈ Set.Ioo (0 : ℝ) 1,
      Istar lam mu θ x0 (a * γ₁ + (1 - a) * γ₂) T ≤
        ENNReal.ofReal a * Istar lam mu θ x0 γ₁ T
          + ENNReal.ofReal (1 - a) * Istar lam mu θ x0 γ₂ T) ∧
    Istar lam mu θ x0 (gammaStar lam mu θ x0 T) T = 0 ∧
    AntitoneOn (fun γ => Istar lam mu θ x0 γ T) (Set.Icc 0 (gammaStar lam mu θ x0 T)) ∧
    MonotoneOn (fun γ => Istar lam mu θ x0 γ T) (Set.Ici (gammaStar lam mu θ x0 T)) := by sorry

end RenegingLD.MM1
