-- Prove2me | Theorems.Thm_RiskFunctionals_Duality_acceptability_representation
-- name    : RiskFunctionals.Duality.acceptability_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:06.786753+00:00
-- url     : https://prove2.me/theorems/7d876dbd-9c42-4b21-bbc2-f2a85642e0e7
-- title:
--   Corollary 2.32 — dual representation (2.11) of proper u.s.c. acceptability functionals, and its converse
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a non-atomic probability space, $1\le p<\infty$, $\frac1p+\frac1q=1$, $\mathcal Y=L_p(\Omega,\mathcal F,P)$ and $\mathcal Z=L_q(\Omega,\mathcal F,P)$. For $\mathcal A:\mathcal Y\to[-\infty,+\infty]$ let
--   $$\mathcal A^+(Z)=\inf\{\mathbb E(YZ)-\mathcal A(Y):Y\in\mathcal Y\}$$
--   be its concave conjugate.
--
--   1. If $\mathcal A$ is a proper ($\mathcal A<+\infty$ everywhere, $\mathcal A>-\infty$ somewhere), upper semicontinuous acceptability functional, i.e. it satisfies (A1) translation equivariance, (A2) concavity and (A3) pointwise monotonicity, then for every $Y\in\mathcal Y$
--   $$\mathcal A(Y)=\inf\{\mathbb E(YZ)-\mathcal A^+(Z):\ Z\in\mathcal Z,\ \mathbb EZ=1,\ Z\ge0\}.\tag{2.11}$$
--   2. Conversely, if $\mathcal A(Y)=\inf\{\mathbb E(YZ)-A^+(Z):\mathbb EZ=1,\ Z\ge0\}$ for all $Y$, for some proper functional $A^+:\mathcal Z\to[-\infty,+\infty]$, then $\mathcal A$ is upper semicontinuous and satisfies (A1)–(A3).
--
--   The corollary characterizes acceptability functionals: up to semicontinuity they are exactly the infima of the expectations $\mathbb E(YZ)$ under probability densities $Z$, penalized by a concave function of $Z$. It is the profit-side form of the dual representation of convex risk measures.
--
--   **Formalization Note** Functionals are `EReal`-valued; "proper" is the concave notion of p. 270, the reading under which "proper u.s.c. acceptability functional" makes sense for a functional that may take $-\infty$ (§2.2.1). Upper semicontinuity is for the norm topology of $L_p$. $Z\ge0$ means almost surely; the infimum is taken in $[-\infty,+\infty]$ over the densities in $L_q$, so terms with $\mathcal A^+(Z)=-\infty$ contribute $+\infty$. In the converse, $A^+$ is an arbitrary proper functional, not assumed to be the conjugate of $\mathcal A$, and the conclusion is exactly u.s.c. and (A1)–(A3), which is what the page states. The book's "Definition 17" is its Definition 2.17. The non-atomic hypothesis is the book's standing assumption (p. 4). A formalization in which the infimum ranges over all of $L_q$, or in which $\mathcal A^+$ is replaced by a real-valued function, would drop the content of the corollary; neither is used.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 47, Corollary 2.32 (first paragraph), Eq. (2.11)

import Mathlib
import Definitions.Def_RiskFunctionals_Duality_Functionals
import Definitions.Def_RiskFunctionals_Duality_Conjugates

namespace RiskFunctionals.Duality

open MeasureTheory ProbabilityTheory

/-- Corollary 2.32, first paragraph (Pflug & Römisch, p. 47), on `𝒴 = L_p`, `𝒵 = L_q`,
`1 ≤ p < ∞`, `1/p + 1/q = 1`, over a non-atomic probability space. A proper u.s.c.
acceptability functional has the representation
`𝒜(Y) = inf{𝔼(Y Z) − 𝒜⁺(Z) : 𝔼Z = 1, Z ≥ 0}` (2.11), with `𝒜⁺` the concave conjugate.
Conversely, if `𝒜` can be represented as (2.11) for a proper functional `𝒜⁺`, then `𝒜` is
u.s.c. and satisfies (A1)–(A3). -/
theorem acceptability_representation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P) (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [p.HolderConjugate q] :
    (∀ A : Lp ℝ p P → EReal, IsProperConcave A → UpperSemicontinuous A →
      IsAcceptabilityFunctional P A →
      ∀ Y : Lp ℝ p P, A Y = ⨅ Z ∈ {Z : Lp ℝ q P | expectation Z = 1 ∧ ∀ᵐ ω ∂P, 0 ≤ Z ω},
        ((pairing Y Z : ℝ) : EReal) - concaveConj q A Z) ∧
    (∀ (A : Lp ℝ p P → EReal) (Aplus : Lp ℝ q P → EReal), IsProperConcave Aplus →
      (∀ Y : Lp ℝ p P, A Y = ⨅ Z ∈ {Z : Lp ℝ q P | expectation Z = 1 ∧ ∀ᵐ ω ∂P, 0 ≤ Z ω},
        ((pairing Y Z : ℝ) : EReal) - Aplus Z) →
      UpperSemicontinuous A ∧ IsAcceptabilityFunctional P A) := by sorry

end RiskFunctionals.Duality
