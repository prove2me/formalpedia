-- Prove2me | Theorems.Thm_RiskFunctionals_Duality_conjugate_necessary
-- name    : RiskFunctionals.Duality.conjugate_necessary
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:19.626107+00:00
-- url     : https://prove2.me/theorems/a2933d52-a204-470f-b427-af8b25e9c956
-- title:
--   Theorem 2.31 — necessary conditions on the conjugate of a functional in standard form
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a non-atomic probability space, $1\le p<\infty$, $\frac1p+\frac1q=1$, $\mathcal Y=L_p$, $\mathcal Z=L_q$.
--
--   Let $\mathcal A:\mathcal Y\to[-\infty,+\infty)$ be a proper concave functional of the form
--   $$\mathcal A(Y)=\inf\{\mathbb E(YZ)-\mathcal A^+(Z):Z\in\mathcal Z\},\qquad \mathcal A^+(Z)=\inf\{\mathbb E(YZ)-\mathcal A(Y):Y\in\mathcal Y\}.$$
--   Then:
--
--   1. (i) if $\mathcal A$ is translation-equivariant, $\mathcal A^+(Z)>-\infty$ implies $\mathbb E(Z)=1$;
--   2. (ii) if $\mathcal A$ is positively homogeneous, $\mathcal A^+$ takes only the values $0$ or $-\infty$;
--   3. (iii) if $\mathcal A$ is pointwise monotonic, $\mathcal A^+(Z)=-\infty$ for every $Z$ with $P\{Z<0\}>0$;
--   4. (iv) if $\mathcal A$ is version-independent and antitonic with respect to conditional expectation, $\mathcal A(\mathbb E(Y|\mathcal F_1))\ge\mathcal A(Y)$ for all $Y$ and all sub-σ-fields $\mathcal F_1$, then $\mathcal A^+$ is also antitonic with respect to conditional expectation: $\mathcal A^+(\mathbb E(Z|\mathcal F_1))\ge\mathcal A^+(Z)$.
--
--   Let $\mathcal D:\mathcal Y\to(-\infty,+\infty]$ be a proper convex functional of the form
--   $$\mathcal D(Y)=\sup\{\mathbb E(YZ)-\mathcal D^*(Z):Z\in\mathcal Z\},\qquad \mathcal D^*(Z)=\sup\{\mathbb E(YZ)-\mathcal D(Y):Y\in\mathcal Y\}.$$
--   Then:
--
--   5. (v) if $\mathcal D$ is translation-invariant, $\mathcal D^*(Z)<\infty$ implies $\mathbb E(Z)=0$;
--   6. (vi) if $\mathcal D$ is positively homogeneous, $\mathcal D^*$ takes only the values $0$ or $\infty$;
--   7. (vii) if $\mathbb E-\mathcal D$ is pointwise monotonic, $\mathcal D^*(Z)=\infty$ for every $Z$ with $P\{Z>1\}>0$.
--
--   Together with Theorem 2.30 these conditions identify the dual domain of an acceptability or deviation risk functional in standard form; Corollary 2.32 is their consequence.
--
--   **Formalization Note** Properness ($\mathcal A<+\infty$ everywhere and $>-\infty$ somewhere; $\mathcal D>-\infty$ everywhere and $<+\infty$ somewhere) is added as the reading of the book's conventions (finding F4: for $\mathcal A\equiv-\infty$, which is of the stated form with $\mathcal A^+\equiv+\infty$, (i) and (iii) fail). In (ii) and (vi) the dichotomy holds pointwise, for each $Z$ separately. Conditional expectations are taken with respect to every sub-σ-algebra of $\mathcal F$, and "$\mathcal A(\mathbb E(Y|\mathcal F_1))$" is the value at the element of $L_p$ a.s. equal to $\mathbb E(Y|\mathcal F_1)$. The non-atomic hypothesis is the book's standing assumption (p. 4).
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 45–46, Theorem 2.31

import Mathlib
import Definitions.Def_RiskFunctionals_Duality_Functionals
import Definitions.Def_RiskFunctionals_Duality_Conjugates

namespace RiskFunctionals.Duality

open MeasureTheory ProbabilityTheory

/-- Theorem 2.31 (Pflug & Römisch, pp. 45–46), on `𝒴 = L_p`, `𝒵 = L_q` over a non-atomic
probability space. For a proper concave `𝒜(Y) = inf{𝔼(Y Z) − 𝒜⁺(Z) : Z ∈ 𝒵}`:
(i) (A1) ⇒ (`𝒜⁺(Z) > −∞` ⇒ `𝔼(Z) = 1`); (ii) (A4) ⇒ `𝒜⁺` takes only the values `0`, `−∞`;
(iii) (A3) ⇒ `𝒜⁺(Z) = −∞` whenever `P{Z < 0} > 0`; (iv) `𝒜` version-independent and antitonic
w.r.t. conditional expectation ⇒ `𝒜⁺` antitonic w.r.t. conditional expectation.
For a proper convex `𝒟(Y) = sup{𝔼(Y Z) − 𝒟*(Z) : Z ∈ 𝒵}`:
(v) (D1) ⇒ (`𝒟*(Z) < ∞` ⇒ `𝔼(Z) = 0`); (vi) (D4) ⇒ `𝒟*` takes only the values `0`, `∞`;
(vii) `𝔼 − 𝒟` pointwise monotonic ⇒ `𝒟*(Z) = ∞` whenever `P{Z > 1} > 0`. -/
theorem conjugate_necessary {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P) (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [p.HolderConjugate q] :
    (∀ A : Lp ℝ p P → EReal, ConcaveFunctional A → IsProperConcave A →
      (∀ Y, A Y = ⨅ Z : Lp ℝ q P, ((pairing Y Z : ℝ) : EReal) - concaveConj q A Z) →
      (TranslationEquivariant P A → ∀ Z, ⊥ < concaveConj q A Z → expectation Z = 1) ∧
      (PositivelyHomogeneous A → ∀ Z, concaveConj q A Z = 0 ∨ concaveConj q A Z = ⊥) ∧
      (PointwiseMonotone P A → ∀ Z : Lp ℝ q P, 0 < P {ω | Z ω < 0} → concaveConj q A Z = ⊥) ∧
      (VersionIndependent P A →
        (∀ m : {m : MeasurableSpace Ω // m ≤ m0}, ∀ Y Y' : Lp ℝ p P,
          (Y' : Ω → ℝ) =ᵐ[P] condExp m.1 P (Y : Ω → ℝ) → A Y ≤ A Y') →
        (∀ m : {m : MeasurableSpace Ω // m ≤ m0}, ∀ Z Z' : Lp ℝ q P,
          (Z' : Ω → ℝ) =ᵐ[P] condExp m.1 P (Z : Ω → ℝ) →
            concaveConj q A Z ≤ concaveConj q A Z'))) ∧
    (∀ D : Lp ℝ p P → EReal, ConvexFunctional D → IsProperConvex D →
      (∀ Y, D Y = ⨆ Z : Lp ℝ q P, ((pairing Y Z : ℝ) : EReal) - convexConj q D Z) →
      (TranslationInvariant P D → ∀ Z, convexConj q D Z < ⊤ → expectation Z = 0) ∧
      (PositivelyHomogeneous D → ∀ Z, convexConj q D Z = 0 ∨ convexConj q D Z = ⊤) ∧
      (MeanMinusMonotone P D → ∀ Z : Lp ℝ q P, 0 < P {ω | 1 < Z ω} →
        convexConj q D Z = ⊤)) := by sorry

end RiskFunctionals.Duality
