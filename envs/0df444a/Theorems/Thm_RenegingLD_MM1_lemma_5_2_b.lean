-- Prove2me | Theorems.Thm_RenegingLD_MM1_lemma_5_2_b
-- name    : RenegingLD.MM1.lemma_5_2_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:15.021864+00:00
-- url     : https://prove2.me/theorems/e20f0aec-a76a-47dc-86d4-b00ac5d5299e
-- title:
--   Lemma 5.2(b), p. 24 — 1 − Ae^{θT} → z_γ, A → 0 and B → z_γ⁻¹ as T → ∞, uniformly for x₀ in compacts
-- statement:
--   Let $\lambda\ge\mu>0$, $\theta>0$ and $\gamma>0$, and let $K\subset\mathbb R_+$ be compact. For $x_0\in K$ and $T>0$ let $A=A(x_0,T)<e^{-\theta T}$ be the root of (5.9) and $B=1/(1-Ae^{\theta T})$. Then, uniformly for $x_0\in K$, as $T\to\infty$,
--   $$1-Ae^{\theta T}\to z_\gamma=\frac{2\lambda}{\gamma+\sqrt{\gamma^2+4\lambda\mu}},\qquad A\to0,\qquad B\to z_\gamma^{-1}.$$
--   Explicitly: for every $\varepsilon>0$ there is $T'$ such that for all $T\ge T'$, all $x_0\in K$ and every root $A<e^{-\theta T}$ of (5.9), $|1-Ae^{\theta T}-z_\gamma|<\varepsilon$, $|A|<\varepsilon$ and $|1/(1-Ae^{\theta T})-z_\gamma^{-1}|<\varepsilon$.
--
--   These limits are what make the cost of the candidate minimizer grow like $C(\gamma)T$ (Lemma 5.6).
--
--   **Formalization Note.** $z_\gamma$ is the first form of (2.10); the equality with $2\lambda/(\gamma+\sqrt{\gamma^2+4\lambda\mu})$ is elementary. "The unique $A$" is rendered as "every $A<e^{-\theta T}$ satisfying (5.9)", which is the same by Lemma 5.2(a).
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 24, Lemma 5.2(b) (preamble 'Suppose γ > 0' on p. 23)

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

theorem lemma_5_2_b (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (γ : ℝ) (hγ : 0 < γ)
    (K : Set ℝ) (hK : IsCompact K) (hK0 : K ⊆ Set.Ici 0) :
    ∀ ε : ℝ, 0 < ε → ∃ T' : ℝ, ∀ T : ℝ, T' ≤ T → ∀ x0 ∈ K, ∀ A : ℝ,
      A < Real.exp (-θ * T) → eq59 lam mu θ γ x0 T A →
        |(1 - A * Real.exp (θ * T)) - z lam mu γ| < ε ∧ |A| < ε ∧
          |1 / (1 - A * Real.exp (θ * T)) - (z lam mu γ)⁻¹| < ε := by sorry

end RenegingLD.MM1
