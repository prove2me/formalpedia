-- Prove2me | Theorems.Thm_RiskFunctionals_Conditional_fenchel_step
-- name    : RiskFunctionals.Conditional.fenchel_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:41.429724+00:00
-- url     : https://prove2.me/theorems/0faa264c-aa74-40e5-90cc-9cf2865655c9
-- title:
--   Eqs. (2.48)–(2.49) — $\mathbb E(\mathcal A(Y)\mathbb 1_B)$ is the infimum of $\mathbb E(YZ)-A_B(Z)$ over all $Z\in L_q$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $\mathcal F_1\subseteq\mathcal F$ a sub-$\sigma$-field, $1\le p<\infty$ and $q$ the conjugate exponent, $1/p+1/q=1$. Let $\mathcal A:L_p(\mathcal F)\to L_p(\mathcal F_1)$ be an upper semicontinuous conditional acceptability mapping and $B\in\mathcal F_1$. Write $h_B(Y)=\mathbb E(\mathcal A(Y)\mathbb 1_B)$ and $A_B(Z)=h_B^+(Z)=\inf\{\mathbb E(YZ)-h_B(Y):Y\in L_p(\mathcal F)\}$ for $Z\in L_q(\mathcal F)$. Then for every $Y\in L_p(\mathcal F)$
--   $$\mathbb E(\mathcal A(Y)\mathbb 1_B)=\inf\{\mathbb E(YZ)-A_B(Z):Z\in L_q(\mathcal F)\}.$$
--
--   This is the unconstrained form of the representation of Theorem 2.51: the real functional $h_B$ is concave and upper semicontinuous, and it coincides with its concave biconjugate over the dual space $L_q(\mathcal F)$ of $L_p(\mathcal F)$.
--
--   **Formalization Note** The infimum is taken in $[-\infty,+\infty]$ (`EReal`) over all of `Lp ℝ q P`, with `p.HolderConjugate q`, `1 ≤ p` and `p ≠ ∞`. $A_B(Z)$ may be $-\infty$; then $\mathbb E(YZ)-A_B(Z)=+\infty$, as in the book. $A_B(Z)$ is never $+\infty$ (it is bounded by the value at any single $Y$), so no $\infty-\infty$ arises.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 68, Eqs. (2.48)–(2.49) (proof of Theorem 2.51)

import Mathlib
import Definitions.Def_RiskFunctionals_Conditional_Mappings

namespace RiskFunctionals.Conditional

open MeasureTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 68,
Eqs. (2.48)–(2.49) (proof of Theorem 2.51): for an upper semicontinuous conditional
acceptability mapping `𝒜 : L_p(ℱ) → L_p(ℱ₁)`, `1 ≤ p < ∞`, `1/p + 1/q = 1`, and `B ∈ ℱ₁`, the
functional `h_B(Y) = 𝔼(𝒜(Y) 𝟙_B)` equals its concave biconjugate:
`h_B(Y) = inf {𝔼(Y Z) − h_B⁺(Z) : Z ∈ L_q(ℱ)}` with `h_B⁺(Z) = inf {𝔼(Y Z) − h_B(Y) : Y ∈ 𝒴}`
(`= A_B(Z)`, `dualFunction`). Infima in `EReal`. -/
theorem fenchel_step {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (P : Measure[mΩ] Ω) [IsProbabilityMeasure P]
    (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤) [p.HolderConjugate q]
    (A : Lp ℝ p P → lpMeas ℝ ℝ m p P) (hA : IsConditionalAcceptabilityMapping A)
    (husc : IsUpperSemicontinuousMapping A)
    (B : Set Ω) (hB : MeasurableSet[m] B) (Y : Lp ℝ p P) :
    ((∫ ω in B, (A Y : Lp ℝ p P) ω ∂P : ℝ) : EReal)
      = ⨅ Z : Lp ℝ q P, ((pairing Y Z : ℝ) : EReal) - dualFunction A B Z := by sorry

end RiskFunctionals.Conditional
