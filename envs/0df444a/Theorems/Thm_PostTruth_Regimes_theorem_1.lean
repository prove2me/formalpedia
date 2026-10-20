-- Prove2me | Theorems.Thm_PostTruth_Regimes_theorem_1
-- name    : PostTruth.Regimes.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:34.395669+00:00
-- url     : https://prove2.me/theorems/71cecc74-75e0-49da-b792-13d951055559
-- title:
--   Theorem 1 — Bayesian and DeGroot mislearning across misinformation regimes
-- statement:
--   Fix organic-news accuracy $1/2<p\leq1$ and put $q^*=(2p-1)/(2p)$. Then $q^*\in(0,1)$. For every continuous prior-belief law $H$ on $[0,1]$ that is symmetric about $1/2$, and every split law $F$ given by a density on $[0,1]$:
--
--   $$
--   \begin{aligned}
--   0<q<q^*&\implies P_B(\theta)\leq P_D(\theta),\\
--   q^*<q<1/2,\quad H,F\text{ fully supported on }[0,1]
--     &\implies P_D(\theta)<P_B(\theta),
--   \end{aligned}
--   \qquad \theta\in\{L,R\}.
--   $$
--
--   Here $P_B(\theta)$ and $P_D(\theta)$ are the probabilities, over the random split, that the Bayesian or DeGroot society mislearns when the true state is $\theta$. Thus the ordering of the learning rules changes above the stated misinformation threshold under full support.
--
--   **Formalization Note** The proof pins the paper's existential $q^*$ to $(2p-1)/(2p)$. Part (i) uses $\leq$ because both probabilities can be zero, although the printed statement says “lower.” The formulas apply separately to both states. The mean-field beliefs and the tie convention are in the shared model definition.
-- source:
--   Mostagir & Siderius, Learning in a Post-Truth World, SSRN working paper 3879174 (version of 2 July 2021), p. 10, Theorem 1; p. 20, proof and value of q*; https://ssrn.com/abstract=3879174

import Mathlib
import Definitions.Def_PostTruth_Regimes_Model

namespace PostTruth.Regimes

open MeasureTheory

/-- Mostagir–Siderius, Theorem 1, p. 10, with the threshold from its proof on p. 20. -/
theorem theorem_1 (p : ℝ) (hp : (1 / 2 : ℝ) < p ∧ p ≤ 1) :
    0 < qStar p ∧ qStar p < 1 ∧
    ∀ (H : Measure ℝ), PriorLaw H → Symmetric H → ∀ (F : SplitLaw),
      (∀ q : ℝ, 0 < q → q < qStar p → ∀ θ : State,
        probBayes p q H F θ ≤ probDeGroot p q H F θ) ∧
      (∀ q : ℝ, qStar p < q → q < 1 / 2 →
        PriorFullSupportOn H 0 1 → F.FullSupportOn 0 1 →
        ∀ θ : State,
          probDeGroot p q H F θ < probBayes p q H F θ) := by sorry

end PostTruth.Regimes
