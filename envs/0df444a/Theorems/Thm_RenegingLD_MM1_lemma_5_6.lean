-- Prove2me | Theorems.Thm_RenegingLD_MM1_lemma_5_6
-- name    : RenegingLD.MM1.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:33.201047+00:00
-- url     : https://prove2.me/theorems/d7e5294b-674e-4764-b11a-955666457ebe
-- title:
--   Lemma 5.6, p. 27 (closed form as in (5.15)) — the cost of the candidate, and I_T(ξ̄, ζ̄)/T → C(γ) uniformly in x₀ ∈ K
-- statement:
--   Let $\lambda\ge\mu>0$, $\theta>0$, $\gamma>0$, and let $K\subset\mathbb R_+$ be compact. For $x_0\in K$ and $T>0$ let $A<e^{-\theta T}$ be the root of (5.9), $B=1/(1-Ae^{\theta T})$, and $(\bar\xi,\bar\zeta)$ the candidate of Construction 5.3.
--
--   1. There is $T_0\in(0,\infty)$ such that for all $T\ge T_0$ and $x_0\in K$, $I_T(\bar\xi,\bar\zeta)<\infty$ and
--   $$I_T(\bar\xi,\bar\zeta)=(\bar\xi(T)+\gamma T-x_0)\log B-\bar\xi(T)\log\frac{1}{1-Ae^{\theta T}}+x_0\log\frac{1}{1-A}+\lambda T+\mu T-\frac{\lambda B}{\theta}\big[\theta T-A(e^{\theta T}-1)\big]+\frac{\mu}{B\theta}\log\frac{e^{-\theta T}-A}{1-A}.$$
--   2. Uniformly for $x_0\in K$,
--   $$\lim_{T\to\infty}\frac{I_T(\bar\xi,\bar\zeta)}{T}=C(\gamma).$$
--
--   The candidate therefore achieves the conjectured decay rate; together with Lemma 5.7 this gives the limit of $I^*_{\gamma,T}/T$ for $x_0>0$.
--
--   **Formalization Note.** The lemma as printed has $(\gamma T+\bar\zeta(T)-x_0)\log B$ as the first term; its proof on the same page, display (5.15), ends with $(\bar\xi(T)+\gamma T-x_0)\log B$, and a numerical quadrature of the cost agrees with (5.15) and not with the printed form ($\bar\zeta(T)=\gamma T$ by Lemma 5.4, so the printed form would double-count $\gamma T$). The statement uses (5.15). The finiteness of $I_T(\bar\xi,\bar\zeta)$ is stated so that the real-valued identity is meaningful (`toReal` of $\infty$ is $0$). "With $T_0$ as in Lemma 5.5" is rendered as "there is $T_0>0$". The root of (5.9) is quantified, not chosen.
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 27, Lemma 5.6 and its proof (5.15)

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

theorem lemma_5_6 (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (γ : ℝ) (hγ : 0 < γ)
    (K : Set ℝ) (hK : IsCompact K) (hK0 : K ⊆ Set.Ici 0) :
    (∃ T0 : ℝ, 0 < T0 ∧ ∀ T : ℝ, T0 ≤ T → ∀ x0 ∈ K, ∀ A B : ℝ,
      A < Real.exp (-θ * T) → eq59 lam mu θ γ x0 T A →
      B = 1 / (1 - A * Real.exp (θ * T)) →
        IT lam mu θ x0 T (fun t => xiBar lam mu θ x0 A B t)
            (fun t => zetaBar lam mu θ x0 A B t) ≠ ⊤ ∧
        (IT lam mu θ x0 T (fun t => xiBar lam mu θ x0 A B t)
            (fun t => zetaBar lam mu θ x0 A B t)).toReal =
          (xiBar lam mu θ x0 A B T + γ * T - x0) * Real.log B
            - xiBar lam mu θ x0 A B T * Real.log (1 / (1 - A * Real.exp (θ * T)))
            + x0 * Real.log (1 / (1 - A)) + lam * T + mu * T
            - lam * B / θ * (θ * T - A * (Real.exp (θ * T) - 1))
            + mu / (B * θ) * Real.log ((Real.exp (-θ * T) - A) / (1 - A))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ T' : ℝ, ∀ T : ℝ, T' ≤ T → ∀ x0 ∈ K, ∀ A B : ℝ,
      A < Real.exp (-θ * T) → eq59 lam mu θ γ x0 T A →
      B = 1 / (1 - A * Real.exp (θ * T)) →
        IT lam mu θ x0 T (fun t => xiBar lam mu θ x0 A B t)
            (fun t => zetaBar lam mu θ x0 A B t) ≠ ⊤ ∧
        |(IT lam mu θ x0 T (fun t => xiBar lam mu θ x0 A B t)
            (fun t => zetaBar lam mu θ x0 A B t)).toReal / T - C lam mu γ| < ε) := by sorry

end RenegingLD.MM1
