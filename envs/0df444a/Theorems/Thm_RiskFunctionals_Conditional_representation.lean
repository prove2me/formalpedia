-- Prove2me | Theorems.Thm_RiskFunctionals_Conditional_representation
-- name    : RiskFunctionals.Conditional.representation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:46.666002+00:00
-- url     : https://prove2.me/theorems/6af6c229-0f17-4d48-b2b3-55dff5fec3a4
-- title:
--   Theorem 2.51 — dual representation of upper semicontinuous conditional acceptability mappings
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $\mathcal F_1\subseteq\mathcal F$ a sub-$\sigma$-field, $1\le p<\infty$ and $1/p+1/q=1$. Let $\mathcal A:L_p(\mathcal F)\to L_p(\mathcal F_1)$ be an upper semicontinuous conditional acceptability mapping. For $B\in\mathcal F_1$ and $Z\in L_q(\mathcal F)$ let
--   $$A_B(Z)=\inf\{\mathbb E(YZ)-\mathbb E(\mathcal A(Y)\mathbb 1_B):Y\in L_p(\mathcal F)\}.\tag{2.46}$$
--
--   1. For every $Y\in L_p(\mathcal F)$ and $B\in\mathcal F_1$,
--   $$\mathbb E(\mathcal A(Y)\mathbb 1_B)=\inf_{Z\in L_q(\mathcal F)}\{\mathbb E(YZ)-A_B(Z):Z\ge0,\ \mathbb E(Z\mid\mathcal F_1)=\mathbb 1_B\}.\tag{2.45}$$
--   2. If $\mathcal A$ is positively homogeneous then, for every $B\in\mathcal F_1$, with $S_B=\{Z\in L_q(\mathcal F):A_B(Z)\ge0\}$, one has $A_B(Z)=0$ for $Z\in S_B$ and $A_B(Z)=-\infty$ for $Z\notin S_B$, and for every $Y\in L_p(\mathcal F)$
--   $$\mathbb E(\mathcal A(Y)\mathbb 1_B)=\inf_{Z\in S_B}\{\mathbb E(YZ):Z\ge0,\ \mathbb E(Z\mid\mathcal F_1)=\mathbb 1_B\}.\tag{2.47}$$
--
--   The theorem is the conditional analogue of the dual representation of acceptability functionals: the conditional mapping is determined by its integrals over the observable events $B$, and each of these is an infimum of linear functionals over densities whose conditional expectation is the indicator of $B$, exactly as in the defining relation of the conditional expectation.
--
--   **Formalization Note** All infima are in `EReal`, over `Lp ℝ q P`, and all constraints hold almost surely; $\mathbb E(Z\mid\mathcal F_1)$ is Mathlib's `P[Z|m]` with `m ≤ mΩ`. The difference $\mathbb E(YZ)-A_B(Z)$ has a real first term, so it is $+\infty$ when $A_B(Z)=-\infty$ and is never of the form $\infty-\infty$. Upper semicontinuity is that of each real functional $Y\mapsto\mathbb E(\mathcal A(Y)\mathbb 1_B)$, $B\in\mathcal F_1$, as the book defines it, not of the map into $L_p(\mathcal F_1)$.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 67–68, Theorem 2.51

import Mathlib
import Definitions.Def_RiskFunctionals_Conditional_Mappings

namespace RiskFunctionals.Conditional

open MeasureTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007,
pp. 67–68, Theorem 2.51. Let `𝒜 : L_p(ℱ) → L_p(ℱ₁)` (`1 ≤ p < ∞`, `ℱ₁ ⊆ ℱ`) be an upper
semicontinuous conditional acceptability mapping and `1/p + 1/q = 1`.
1. (2.45)–(2.46): for every `Y ∈ 𝒴` and `B ∈ ℱ₁`,
   `𝔼(𝒜(Y) 𝟙_B) = inf_{Z ∈ L_q(ℱ)} {𝔼(Y Z) − A_B(Z) : Z ≥ 0, 𝔼(Z|ℱ₁) = 𝟙_B}`,
   with `A_B(Z) = inf {𝔼(Y Z) − 𝔼(𝒜(Y) 𝟙_B) : Y ∈ 𝒴}` (`dualFunction`).
2. If `𝒜` is positively homogeneous then, for every `B ∈ ℱ₁`, `A_B(Z) = 0` for `Z ∈ S_B`,
   `A_B(Z) = −∞` otherwise, where `S_B = {Z ∈ L_q(ℱ) : A_B(Z) ≥ 0}` (`dualSet`), and (2.47)
   `𝔼(𝒜(Y) 𝟙_B) = inf_{Z ∈ S_B} {𝔼(Y Z) : Z ≥ 0, 𝔼(Z|ℱ₁) = 𝟙_B}` for every `Y ∈ 𝒴`.
All infima are in `EReal`. -/
theorem representation {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (P : Measure[mΩ] Ω) [IsProbabilityMeasure P]
    (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤) [p.HolderConjugate q]
    (A : Lp ℝ p P → lpMeas ℝ ℝ m p P) (hA : IsConditionalAcceptabilityMapping A)
    (husc : IsUpperSemicontinuousMapping A) :
    (∀ (Y : Lp ℝ p P) (B : Set Ω), MeasurableSet[m] B →
      ((∫ ω in B, (A Y : Lp ℝ p P) ω ∂P : ℝ) : EReal)
        = ⨅ (Z : Lp ℝ q P) (_ : IsConditionalDensity m P B Z),
            ((pairing Y Z : ℝ) : EReal) - dualFunction A B Z) ∧
    (IsPositivelyHomogeneous A →
      ∀ B : Set Ω, MeasurableSet[m] B →
        (∀ Z ∈ dualSet q A B, dualFunction A B Z = 0) ∧
        (∀ Z : Lp ℝ q P, Z ∉ dualSet q A B → dualFunction A B Z = ⊥) ∧
        (∀ Y : Lp ℝ p P,
          ((∫ ω in B, (A Y : Lp ℝ p P) ω ∂P : ℝ) : EReal)
            = ⨅ Z ∈ dualSet q A B, ⨅ (_ : IsConditionalDensity m P B Z),
                ((pairing Y Z : ℝ) : EReal))) := by sorry

end RiskFunctionals.Conditional
