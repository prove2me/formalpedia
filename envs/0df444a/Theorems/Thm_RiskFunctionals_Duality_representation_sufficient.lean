-- Prove2me | Theorems.Thm_RiskFunctionals_Duality_representation_sufficient
-- name    : RiskFunctionals.Duality.representation_sufficient
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:12.232959+00:00
-- url     : https://prove2.me/theorems/33d1fe19-912f-45ba-aad3-257bc194caa3
-- title:
--   Theorem 2.30 (A)(i)–(iv), (B)(vi)–(ix) — properties of a functional read off its dual representation
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a non-atomic probability space, $1\le p<\infty$, $\frac1p+\frac1q=1$, $\mathcal Y=L_p$, $\mathcal Z=L_q$.
--
--   **(A)** Let $\mathcal A:\mathcal Y\to[-\infty,+\infty)$ have the representation
--   $$\mathcal A(Y)=\inf\{\mathbb E(YZ)-A(Z):Z\in\mathcal Z_{\mathcal A}\},$$
--   with $\mathcal Z_{\mathcal A}\subseteq\mathcal Z$ and $A:\mathcal Z\to[-\infty,+\infty]$ satisfying $A(Z)>-\infty$ for $Z\in\mathcal Z_{\mathcal A}$. Then:
--
--   1. (i) if $\mathbb E(Z)=1$ for all $Z\in\mathcal Z_{\mathcal A}$, $\mathcal A$ is translation-equivariant (A1);
--   2. (ii) if $A=0$, $\mathcal A$ is positively homogeneous (A4);
--   3. (iii) if $A$ and $\mathcal Z_{\mathcal A}$ are version-independent — whenever $Z$ and $\tilde Z$ have the same distribution, $A(Z)=A(\tilde Z)$ and either both or neither lie in $\mathcal Z_{\mathcal A}$ — then $\mathcal A$ is version-independent;
--   4. (iv) if all $Z\in\mathcal Z_{\mathcal A}$ are nonnegative, $\mathcal A$ is pointwise monotonic (A3); if in addition $\mathcal A$ is version-independent, then $Y^{(1)}\prec_{FSD}Y^{(2)}$ implies $\mathcal A(Y^{(1)})\le\mathcal A(Y^{(2)})$.
--
--   **(B)** Let $\mathcal D:\mathcal Y\to(-\infty,+\infty]$ have the representation
--   $$\mathcal D(Y)=\sup\{\mathbb E(YZ)-D(Z):Z\in\mathcal Z_{\mathcal D}\},$$
--   with $D(Z)<\infty$ for $Z\in\mathcal Z_{\mathcal D}$. Then:
--
--   5. (vi) if $\mathbb E(Z)=0$ for all $Z\in\mathcal Z_{\mathcal D}$, $\mathcal D$ is translation-invariant (D1);
--   6. (vii) if $D=0$, $\mathcal D$ is positively homogeneous (D4);
--   7. (viii) if $D$ and $\mathcal Z_{\mathcal D}$ are version-independent, $\mathcal D$ is version-independent;
--   8. (ix) if all $Z\in\mathcal Z_{\mathcal D}$ satisfy $Z\le1$, $\mathcal D$ satisfies (D3).
--
--   These are the sufficient conditions by which the properties of an acceptability or deviation functional are verified from a dual representation; Theorem 2.31 gives the converse conditions for representations in standard form.
--
--   **Formalization Note** Parts (A)(v) and (B)(x) (isotonicity with respect to $\prec_{SSD}$ and convex dominance) are not included. $\mathcal A\ne+\infty$ and $\mathcal D\ne-\infty$ everywhere are the book's conventions (§2.2.1, p. 39; p. 27: a functional takes $+\infty$ or $-\infty$ but not both); without them (ii) and (vii) fail at $\lambda=0$ for an empty dual set. "$D(Z)<\infty$ for $Z\in\mathcal Z$" in (B) is read as for $Z\in\mathcal Z_{\mathcal D}$, mirroring (A). Infima and suprema are taken in $[-\infty,+\infty]$; the non-atomic hypothesis, printed in (A), is the book's standing assumption (p. 4) and is applied to (B) as well. Distributions of $Y$ are compared through their laws on $\mathbb R$; $\prec_{FSD}$ is Definition 1.10(i).
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 43–44, Theorem 2.30 (A)(i)–(iv), (B)(vi)–(ix)

import Mathlib
import Definitions.Def_RiskFunctionals_Duality_Functionals
import Definitions.Def_RiskFunctionals_Duality_Conjugates

namespace RiskFunctionals.Duality

open MeasureTheory ProbabilityTheory

/-- Theorem 2.30 (Pflug & Römisch, pp. 43–44), parts (A)(i)–(iv) and (B)(vi)–(ix), on
`𝒴 = L_p`, `𝒵 = L_q` over a non-atomic probability space.
(A) If `𝒜(Y) = inf{𝔼(Y Z) − A(Z) : Z ∈ 𝒵_𝒜}` with `A(Z) > −∞` on `𝒵_𝒜`, then
(i) `𝔼(Z) = 1` on `𝒵_𝒜` ⇒ (A1); (ii) `A = 0` ⇒ (A4); (iii) `A`, `𝒵_𝒜` version-independent ⇒
`𝒜` version-independent; (iv) `Z ≥ 0` on `𝒵_𝒜` ⇒ (A3), and then, if `𝒜` is version-independent,
`𝒜` is monotonic w.r.t. `≺_FSD`.
(B) If `𝒟(Y) = sup{𝔼(Y Z) − D(Z) : Z ∈ 𝒵_𝒟}` with `D(Z) < ∞` on `𝒵_𝒟`, then
(vi) `𝔼(Z) = 0` on `𝒵_𝒟` ⇒ (D1); (vii) `D = 0` ⇒ (D4); (viii) `D`, `𝒵_𝒟` version-independent ⇒
`𝒟` version-independent; (ix) `Z ≤ 1` on `𝒵_𝒟` ⇒ (D3). -/
theorem representation_sufficient {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P) (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [p.HolderConjugate q] :
    (∀ (A : Lp ℝ p P → EReal) (Adual : Lp ℝ q P → EReal) (ZA : Set (Lp ℝ q P)),
      (∀ Z ∈ ZA, Adual Z ≠ ⊥) → (∀ Y, A Y ≠ ⊤) →
      (∀ Y, A Y = ⨅ Z ∈ ZA, ((pairing Y Z : ℝ) : EReal) - Adual Z) →
      ((∀ Z ∈ ZA, expectation Z = 1) → TranslationEquivariant P A) ∧
      ((∀ Z, Adual Z = 0) → PositivelyHomogeneous A) ∧
      ((∀ Z Z' : Lp ℝ q P, IdentDistrib Z Z' P P → Adual Z = Adual Z' ∧ (Z ∈ ZA ↔ Z' ∈ ZA)) →
        VersionIndependent P A) ∧
      ((∀ Z ∈ ZA, ∀ᵐ ω ∂P, 0 ≤ Z ω) →
        PointwiseMonotone P A ∧
        (VersionIndependent P A →
          ∀ Y₁ Y₂ : Lp ℝ p P, FSD (P.map Y₁) (P.map Y₂) → A Y₁ ≤ A Y₂))) ∧
    (∀ (D : Lp ℝ p P → EReal) (Ddual : Lp ℝ q P → EReal) (ZD : Set (Lp ℝ q P)),
      (∀ Z ∈ ZD, Ddual Z ≠ ⊤) → (∀ Y, D Y ≠ ⊥) →
      (∀ Y, D Y = ⨆ Z ∈ ZD, ((pairing Y Z : ℝ) : EReal) - Ddual Z) →
      ((∀ Z ∈ ZD, expectation Z = 0) → TranslationInvariant P D) ∧
      ((∀ Z, Ddual Z = 0) → PositivelyHomogeneous D) ∧
      ((∀ Z Z' : Lp ℝ q P, IdentDistrib Z Z' P P → Ddual Z = Ddual Z' ∧ (Z ∈ ZD ↔ Z' ∈ ZD)) →
        VersionIndependent P D) ∧
      ((∀ Z ∈ ZD, ∀ᵐ ω ∂P, Z ω ≤ 1) → MeanMinusMonotone P D)) := by sorry

end RiskFunctionals.Duality
