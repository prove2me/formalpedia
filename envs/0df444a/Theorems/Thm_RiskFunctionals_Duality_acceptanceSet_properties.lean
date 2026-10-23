-- Prove2me | Theorems.Thm_RiskFunctionals_Duality_acceptanceSet_properties
-- name    : RiskFunctionals.Duality.acceptanceSet_properties
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:50:58.645726+00:00
-- url     : https://prove2.me/theorems/c6aa6b8e-9112-4fc9-9492-eb2a0bd1388d
-- title:
--   Proposition 2.26 — from a translation-equivariant functional to its acceptance set
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a non-atomic probability space, $1\le p<\infty$, and $\mathcal A:L_p(\Omega,\mathcal F,P)\to[-\infty,+\infty)$ a translation-equivariant functional, (A1) $\mathcal A(Y+c)=\mathcal A(Y)+c$. Let
--   $$\mathcal S_{\mathcal A}=\{Y:\mathcal A(Y)\ge0\}$$
--   be its acceptance set. Then:
--
--   1. if $\mathcal A$ is upper semicontinuous, $\mathcal S_{\mathcal A}$ is closed;
--   2. if $\mathcal A$ is concave (A2), $\mathcal S_{\mathcal A}$ is convex;
--   3. if $\mathcal A$ is pointwise monotonic (A3), $\mathcal S_{\mathcal A}$ is monotone: $Y^{(1)}\in\mathcal S_{\mathcal A}$ and $Y^{(1)}\le Y^{(2)}$ imply $Y^{(2)}\in\mathcal S_{\mathcal A}$;
--   4. if $\mathcal A$ is positively homogeneous (A4), $\mathcal S_{\mathcal A}$ is a cone: $Y\in\mathcal S_{\mathcal A}$ implies $\lambda Y\in\mathcal S_{\mathcal A}$ for $\lambda\ge0$;
--   5. if $\mathcal A$ is strict (A5), then $\mathbb E(Y)<0$ implies $Y\notin\mathcal S_{\mathcal A}$.
--
--   Each property of the functional is thus inherited by its acceptance set; with Proposition 2.27 this lets one pass back and forth between a functional and its acceptance set.
--
--   **Formalization Note** $\mathcal A$ is `EReal`-valued with $\mathcal A(Y)\ne+\infty$ for all $Y$ (the convention of §2.2.1, p. 39: $\mathcal A$ may take $-\infty$ but not $+\infty$), and translation equivariance is a standing hypothesis (the page introduces $\mathcal S_{\mathcal A}$ for a translation-equivariant functional). Upper semicontinuity is for the norm topology of $L_p$. The non-atomic hypothesis is the book's standing assumption (p. 4).
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 40, Proposition 2.26

import Mathlib
import Definitions.Def_RiskFunctionals_Duality_Functionals

namespace RiskFunctionals.Duality

open MeasureTheory ProbabilityTheory

/-- Proposition 2.26 (Pflug & Römisch, p. 40): from a translation-equivariant functional
`𝒜 : L_p → [−∞, ∞)` to its acceptance set `𝒮_𝒜 = {Y : 𝒜(Y) ≥ 0}`.
(i) `𝒜` u.s.c. ⇒ `𝒮_𝒜` closed; (ii) (A2) ⇒ `𝒮_𝒜` convex; (iii) (A3) ⇒ `𝒮_𝒜` monotone;
(iv) (A4) ⇒ `𝒮_𝒜` a cone; (v) (A5) ⇒ `𝔼(Y) < 0` implies `Y ∉ 𝒮_𝒜`. -/
theorem acceptanceSet_properties {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (A : Lp ℝ p P → EReal) (hA1 : TranslationEquivariant P A) (hA_ne_top : ∀ Y, A Y ≠ ⊤) :
    (UpperSemicontinuous A → IsClosed (acceptanceSet A)) ∧
    (ConcaveFunctional A → _root_.Convex ℝ (acceptanceSet A)) ∧
    (PointwiseMonotone P A → MonotoneSet P (acceptanceSet A)) ∧
    (PositivelyHomogeneous A → IsConeSet (acceptanceSet A)) ∧
    (Strict A → ∀ Y : Lp ℝ p P, expectation Y < 0 → Y ∉ acceptanceSet A) := by sorry

end RiskFunctionals.Duality
