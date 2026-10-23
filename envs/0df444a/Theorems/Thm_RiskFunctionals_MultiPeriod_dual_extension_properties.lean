-- Prove2me | Theorems.Thm_RiskFunctionals_MultiPeriod_dual_extension_properties
-- name    : RiskFunctionals.MultiPeriod.dual_extension_properties
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:59.900151+00:00
-- url     : https://prove2.me/theorems/ec3e78ef-352f-43b1-acb2-4839dec1f15f
-- title:
--   Proposition 3.10 — properties of the dual extension of a single-period acceptability functional
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $p\in[1,\infty]$, $1/p+1/q=1$, $A:L_q\to[-\infty,+\infty]$ and $\mathcal Z_{\mathcal A}=\{Z\in L_q:A(Z)>-\infty\}$ its supergradient set (p. 43). Let $\mathcal A(Y)$ be the functional (3.7) and $\mathcal A(Y;\mathcal F_1)$ its dual extension (3.8). Then, for every sub-σ-algebra $\mathcal F_1\subseteq\mathcal F$:
--
--   1. $\mathcal A(Y;\mathcal F_1)$ is information monotone: $\mathcal F_1'\subseteq\mathcal F_1\subseteq\mathcal F$ implies $\mathcal A(Y;\mathcal F_1')\le\mathcal A(Y;\mathcal F_1)$;
--   2. $\mathcal A(Y)=\mathcal A(Y;\mathcal F_0)$, where $\mathcal F_0=\{\emptyset,\Omega\}$;
--   3. if $Y$ is $\mathcal F_1$-measurable and $A$ is isotonic w.r.t. concave dominance, then
--   $$\mathcal A(Y;\mathcal F_1)=\mathbb E(Y)-A(\mathbb 1),$$
--   where $\mathbb 1$ is the constant function $1$;
--   4. $\mathcal A$ is predictable translation-equivariant: $\mathcal A(Y+C;\mathcal F_1)=\mathbb E(C)+\mathcal A(Y;\mathcal F_1)$ if $C\in L_p$ is $\mathcal F_1$-measurable.
--
--   The proposition shows that the dual extension adds information to a single-period functional in the way §3.1.3 asks: more information never lowers acceptability, and information-measurable cash flows are valued at their expectation.
--
--   **Formalization Note** "$Y$ is $\mathcal F_1$-measurable" for an element of $L_p$ means it has an $\mathcal F_1$-measurable version (membership in Mathlib's `lpMeas`). The infima are in `EReal`. $A(\mathbb 1)$ is $A$ evaluated at the constant $1$ in $L_q$. $\mathcal Z_{\mathcal A}$ is the supergradient set $\{A>-\infty\}$ of p. 43, the book's definition of the symbol, not an arbitrary set.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 129–130, Proposition 3.10

import Mathlib
import Definitions.Def_RiskFunctionals_MultiPeriod_DualExtension

namespace RiskFunctionals.MultiPeriod

open MeasureTheory

/-- Proposition 3.10 (Pflug & Römisch, pp. 129–130), on `𝒴 = L_p(Ω, ℱ, P)`, `𝒵 = L_q(Ω, ℱ, P)`,
`1/p + 1/q = 1`. For a functional of the form (3.7), `𝒜(Y) = inf{𝔼(Y Z) − A(Z) : 𝔼(Z) = 1,
Z ∈ 𝒵_𝒜}` with `𝒵_𝒜 = {Z : A(Z) > −∞}` the supergradient set of `A` (p. 43), the dual
extension (3.8), `𝒜(Y; ℱ₁) = inf{𝔼(Y Z) − A(Z) : 𝔼(Z | ℱ₁) = 1, Z ∈ 𝒵_𝒜}`,
satisfies, for every sub-σ-algebra `ℱ₁ ⊆ ℱ` (the argument `m₁`):
(i) `𝒜(Y; ℱ₁)` is information monotone (Definition 3.6);
(ii) `𝒜(Y) = 𝒜(Y; ℱ₀)` for the trivial σ-algebra `ℱ₀ = {∅, Ω}`;
(iii) if `Y` is `ℱ₁`-measurable and `A` is isotonic w.r.t. concave dominance, then
`𝒜(Y; ℱ₁) = 𝔼(Y) − A(𝟙)`;
(iv) `𝒜(Y + C; ℱ₁) = 𝔼(C) + 𝒜(Y; ℱ₁)` if `C` is `ℱ₁`-measurable. -/
theorem dual_extension_properties {Ω : Type*} (m₁ : MeasurableSpace Ω) [m0 : MeasurableSpace Ω]
    (hm₁ : m₁ ≤ m0) (P : Measure Ω) [IsProbabilityMeasure P] (p q : ENNReal) [Fact (1 ≤ p)]
    [p.HolderConjugate q] (A : Lp ℝ q P → EReal) :
    IsInformationMonotoneSP (fun m (Y : Lp ℝ p P) => dualExtension A m Y) ∧
    (∀ Y : Lp ℝ p P, dualForm A Y = dualExtension A ⊥ Y) ∧
    (IsIsotonicCCD A →
      ∀ Y : Lp ℝ p P, Y ∈ lpMeas ℝ ℝ m₁ p P →
        dualExtension A m₁ Y = ((∫ ω, (Y : Ω → ℝ) ω ∂P : ℝ) : EReal) - A (Lp.const q P 1)) ∧
    (∀ Y C : Lp ℝ p P, C ∈ lpMeas ℝ ℝ m₁ p P →
        dualExtension A m₁ (Y + C) =
          ((∫ ω, (C : Ω → ℝ) ω ∂P : ℝ) : EReal) + dualExtension A m₁ Y) := by sorry

end RiskFunctionals.MultiPeriod
