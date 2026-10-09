-- Prove2me | Theorems.Thm_SLPricing_PreAnn_eq_2_no_sl_threshold
-- name    : SLPricing.PreAnn.eq_2_no_sl_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:16:00.754649+00:00
-- url     : https://prove2.me/theorems/aaeb77ef-df42-4d16-8c7b-8939647ad83c
-- title:
--   (2), p. 11 — without social learning, every purchasing equilibrium is $[\tau(p_1,p_2),1]$ up to a null set
-- statement:
--   Consider pre-announced pricing in the absence of social learning ($\gamma=0$). Fix a plan $\{p_1,p_2\}$ with $p_1\ge 0$, and exclude the single degenerate case $\delta_c=1$, $p_1=p_2$. Define
--   $$\tau(p_1,p_2)=\begin{cases}p_1 & \text{if } p_1\le p_2,\\[2pt] \dfrac{p_1-\delta_c p_2}{1-\delta_c} & \text{if } p_1>p_2 \text{ and } p_1-\delta_c p_2\le 1-\delta_c,\\[4pt] 1 & \text{if } p_1>p_2 \text{ and } p_1-\delta_c p_2> 1-\delta_c.\end{cases}$$
--   Then a purchasing equilibrium exists, and every purchasing equilibrium $B$ coincides with $[\tau(p_1,p_2),1]$ up to a set of Lebesgue measure zero. That is, consumer $x$ buys in the first period iff $x\ge\tau(p_1,p_2)$.
--
--   This is the benchmark consumer response of §5.1, from which the no-SL optimal plan of Proposition 1 is computed.
--
--   **Formalization Note** In the second case $\delta_c<1$ holds automatically. The degenerate plan $p_1=p_2$ at $\delta_c=1$ makes every type indifferent, so every measurable subset of $[p_1,1]$ is an equilibrium; it is excluded. The paper's statement is for "any arbitrary price plan"; the hypothesis $p_1\ge 0$ is added because for $p_1<0$ the interval $[\tau,1]$ contains negative types that do not exist.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), §5.1, (2), p. 11

import Mathlib
import Definitions.Def_SLPricing_PreAnn_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.PreAnn

/-- (2), §5.1, p. 11: without social learning (`γ = 0`), for any plan `{p₁, p₂}` with `p₁ ≥ 0`
a purchasing equilibrium exists, and every purchasing equilibrium is, up to a null set, the set
`[τ(p₁, p₂), 1]` of types above the threshold
`τ = p₁` if `p₁ ≤ p₂`; `(p₁ − δc p₂)/(1 − δc)` if `p₁ > p₂` and `p₁ − δc p₂ ≤ 1 − δc`;
`1` if `p₁ > p₂` and `p₁ − δc p₂ > 1 − δc`.
The degenerate plan `p₁ = p₂` at `δc = 1` (every type indifferent) is excluded. -/
theorem eq_2_no_sl_threshold (P : Params) (hP : P.Standing) (p₁ p₂ : ℝ) (hp₁ : 0 ≤ p₁)
    (hdeg : ¬ (P.δc = 1 ∧ p₁ = p₂)) :
    (∃ B : Set ℝ, IsPreEq P.noSL p₁ p₂ B) ∧
      ∀ B : Set ℝ, IsPreEq P.noSL p₁ p₂ B →
        B =ᵐ[volume] Icc
          (if p₁ ≤ p₂ then p₁
            else if p₁ - P.δc * p₂ ≤ 1 - P.δc then (p₁ - P.δc * p₂) / (1 - P.δc) else 1) 1 := by sorry

end SLPricing.PreAnn
