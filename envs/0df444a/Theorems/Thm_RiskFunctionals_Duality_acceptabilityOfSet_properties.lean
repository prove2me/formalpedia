-- Prove2me | Theorems.Thm_RiskFunctionals_Duality_acceptabilityOfSet_properties
-- name    : RiskFunctionals.Duality.acceptabilityOfSet_properties
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:50:58.078264+00:00
-- url     : https://prove2.me/theorems/f4fec84a-4a46-4f56-aaa2-8ccb28ea6107
-- title:
--   Proposition 2.27 — from an acceptance set to the pertaining functional
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a non-atomic probability space, $1\le p<\infty$, $\mathcal S\subseteq L_p(\Omega,\mathcal F,P)$ any set, and
--   $$\mathcal A_{\mathcal S}(Y)=\sup\{a\in\mathbb R: Y-a\in\mathcal S\}\in[-\infty,+\infty].$$
--   Then:
--
--   1. if $\mathcal S$ is closed, $\mathcal A_{\mathcal S}$ is upper semicontinuous;
--   2. $\mathcal A_{\mathcal S}$ is translation-equivariant (A1);
--   3. if $\mathcal S$ is convex, $\mathcal A_{\mathcal S}$ is concave (A2);
--   4. if $\mathcal S$ is monotone, $\mathcal A_{\mathcal S}$ is pointwise monotonic (A3);
--   5. if $\mathcal S$ is a cone, $\mathcal A_{\mathcal S}$ is positively homogeneous (A4), $\mathcal A_{\mathcal S}(\lambda Y)=\lambda\mathcal A_{\mathcal S}(Y)$ for all $\lambda\ge0$;
--   6. if every $Y\in\mathcal S$ has $\mathbb E(Y)\ge0$, $\mathcal A_{\mathcal S}$ is strict (A5).
--
--   This is the converse passage of Proposition 2.26: an acceptance set determines a functional with the corresponding properties.
--
--   **Formalization Note** The supremum is taken in $[-\infty,+\infty]$ ($-\infty$ when no $a$ qualifies, $+\infty$ when the qualifying $a$ are unbounded), since the page does not exclude either case. (A4) is required for every $\lambda\ge0$, with $0\cdot(\pm\infty)=0$, as Definition 2.19 states it. Finding F3 records that clauses (i) and (v) fail as printed; the corrected statement is posed as a separate variant item.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 40–41, Proposition 2.27, Eq. (2.5)

import Mathlib
import Definitions.Def_RiskFunctionals_Duality_Functionals

namespace RiskFunctionals.Duality

open MeasureTheory ProbabilityTheory

/-- Proposition 2.27 (Pflug & Römisch, pp. 40–41): from a set `𝒮 ⊆ L_p` to the functional
`𝒜_𝒮(Y) = sup{a : Y − a ∈ 𝒮}` (2.5), valued in `[−∞, +∞]`.
(i) `𝒮` closed ⇒ `𝒜_𝒮` u.s.c.; (ii) `𝒜_𝒮` satisfies (A1); (iii) `𝒮` convex ⇒ (A2);
(iv) `𝒮` monotone ⇒ (A3); (v) `𝒮` a cone ⇒ (A4); (vi) `𝔼(Y) ≥ 0` on `𝒮` ⇒ (A5). -/
theorem acceptabilityOfSet_properties {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (S : Set (Lp ℝ p P)) :
    (IsClosed S → UpperSemicontinuous (acceptabilityOfSet P S)) ∧
    TranslationEquivariant P (acceptabilityOfSet P S) ∧
    (_root_.Convex ℝ S → ConcaveFunctional (acceptabilityOfSet P S)) ∧
    (MonotoneSet P S → PointwiseMonotone P (acceptabilityOfSet P S)) ∧
    (IsConeSet S → PositivelyHomogeneous (acceptabilityOfSet P S)) ∧
    ((∀ Y ∈ S, 0 ≤ expectation Y) → Strict (acceptabilityOfSet P S)) := by sorry

end RiskFunctionals.Duality
