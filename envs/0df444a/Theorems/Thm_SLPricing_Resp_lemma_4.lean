-- Prove2me | Theorems.Thm_SLPricing_Resp_lemma_4
-- name    : SLPricing.Resp.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:48.293558+00:00
-- url     : https://prove2.me/theorems/fdc1dd19-352c-430b-8f50-2007e59874e6
-- title:
--   Lemma 4, p. 21 — with SL, a unique responsive purchasing equilibrium with first-period threshold $\zeta(p_1)$ solving (7)
-- statement:
--   Consider responsive pricing with social learning ($\gamma>0$). For $\psi\in[0,1]$ let $f(\cdot;\psi)$ be the pre-posterior law of the posterior mean $q_u$ when a mass $1-\psi$ of consumers bought in period 1, and let $p_2^*(q_u,\psi)$ be the second-period price (6). Fix a first-period price $p_1\ge0$ and write $\bar p=\frac{2-\delta_c(1-c)}{2}$. Then an equilibrium exists, and:
--
--   1. If $p_1\le\bar p$, the implicit equation
--   $$\psi-p_1=\delta_c\int_{-\infty}^{\infty}\big(\psi+q_u-p_2^*(q_u,\psi)\big)^+\,f(q_u;\psi)\,dq_u \tag{7}$$
--   has exactly one solution $\psi\in[p_1,1]$; the types $[\psi,1]$ buying in period 1, with an optimal second-period rule, form an equilibrium; and in every equilibrium the set of first-period buyers equals $[\psi,1]$ up to a null set.
--   2. If $p_1>\bar p$ (adoption inertia), the configuration in which nobody buys in period 1 is an equilibrium, and in every equilibrium the set of first-period buyers is null.
--
--   The threshold is $\zeta(p_1)=\psi$ in case 1 and $\zeta(p_1)=1$ in case 2. The lemma describes the consumers' response to every first-period price, which the firm's problem (8) optimizes over.
--
--   **Formalization Note** The integrand with the positive part equals the paper's integrand on $[c-\psi,\infty)$, since $\psi+q_u-p_2^*\le 0$ exactly when $q_u\le c-\psi$. The hypothesis $p_1\ge0$ is added: for $p_1<0$ a threshold below $0$ would correspond to a review mass above $1$. The monotonicity sentence of the lemma (in $\gamma$, $p_1$, $\delta_c$, $c$) is not part of this item. Equilibrium uniqueness is up to null sets of buyers.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Lemma 4, equation (7), p. 21 (proof pp. 31–32)

import Mathlib
import Definitions.Def_SLPricing_Resp_Model
import Definitions.Def_SLPricing_Resp_P2Star
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.Resp

/-- Lemma 4, p. 21 (proof pp. 31–32): with social learning (`γ > 0`) and a first-period price
`p₁ ≥ 0` under responsive pricing, an equilibrium exists. If `p₁ ≤ (2 − δc(1 − c))/2`, the
implicit equation (7) `ψ − p₁ = δc E[(ψ + q_u − p∗₂(q_u, ψ))⁺]`, with `q_u` distributed by the
pre-posterior law for a mass `1 − ψ` of reviews, has exactly one solution `ψ ∈ [p₁, 1]`; the
types `[ψ, 1]` buying early (with an optimal second-period rule) form an equilibrium, and every
equilibrium buyer set equals `[ψ, 1]` up to a null set. If `p₁ > (2 − δc(1 − c))/2` (adoption
inertia), nobody buying early is an equilibrium and every equilibrium buyer set is null. -/
theorem lemma_4 (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) (p₁ : ℝ) (hp₁ : 0 ≤ p₁) :
    (∃ B s, IsRespEq P p₁ B s) ∧
    (p₁ ≤ (2 - P.δc * (1 - P.c)) / 2 →
      ∃ ψ ∈ Icc p₁ 1,
        ψ - p₁ = P.δc * ∫ q, max (ψ + q - p2Star P.c q ψ) 0 ∂(prePost P (1 - ψ)) ∧
        (∀ ψ' ∈ Icc p₁ 1,
          ψ' - p₁ = P.δc * ∫ q, max (ψ' + q - p2Star P.c q ψ') 0 ∂(prePost P (1 - ψ')) →
          ψ' = ψ) ∧
        (∃ s, IsRespEq P p₁ (Icc ψ 1) s) ∧
        ∀ B s, IsRespEq P p₁ B s → B =ᵐ[volume] Icc ψ 1) ∧
    ((2 - P.δc * (1 - P.c)) / 2 < p₁ →
      (∃ s, IsRespEq P p₁ ∅ s) ∧
      ∀ B s, IsRespEq P p₁ B s → volume B = 0) := by sorry

end SLPricing.Resp
