-- Prove2me | Theorems.Thm_ScenarioReduction_Redistribution_Supplement_quantitative_stability
-- name    : ScenarioReduction.Redistribution.Supplement.quantitative_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:31:50.136812+00:00
-- url     : https://prove2.me/theorems/3aeaccb5-6870-42e3-9482-30e69955df4e
-- title:
--   Theorem 1 — quantitative stability of values, solutions and epsilon-solutions (corrected: P_f drops the printed middle inequality, which fails on balls missing X)
-- statement:
--   Let $X\subseteq\mathbb R^n$ be nonempty, closed and convex; let $\Omega\subseteq\mathbb R^s$ be closed with its relative Borel sigma-field; and let $f:\Omega\times\mathbb R^n\to[-\infty,+\infty]$ be measurable in the scenario and lower semicontinuous and convex in the decision. For $Q\in\mathcal P_f$, write $F_Q(x)=E_Qf(\omega,x)$, $v(Q)=\inf_{x\in X}F_Q(x)$ and $S_\varepsilon(Q)=\{x\in X:F_Q(x)\le v(Q)+\varepsilon\}$, with $S=S_0$. Let $d_{f,\rho}$ be the supremum of objective differences over $X\cap\rho\mathbb B$, and $\Psi(\eta)=\eta+\psi^{-1}(2\eta)$ the conditioning modulus defined above.
--
--   If $P\in\mathcal P_f$ and $S(P)$ is nonempty and bounded, there are shared constants $\rho>0$ and $\bar\varepsilon>0$ with the following two properties.
--
--   1. Every $Q\in\mathcal P_f$ with $d_{f,\rho}(P,Q)<\bar\varepsilon$ has finite optimal value, a nonempty solution set, and
--
--   $$|v(P)-v(Q)|\le d_{f,\rho}(P,Q),\qquad S(Q)\subseteq S(P)+\Psi(d_{f,\rho}(P,Q))\mathbb B.$$
--
--   2. For every $0<\varepsilon<\bar\varepsilon$ and every $Q\in\mathcal P_f$ with $d_{f,\rho+\varepsilon}(P,Q)<\varepsilon$, both epsilon-solution sets are nonempty and
--
--   $$dl_\infty(S_\varepsilon(P),S_\varepsilon(Q))\le\frac{2\rho}{\varepsilon}d_{f,\rho+\varepsilon}(P,Q).$$
--
--   This companion theorem gives stability of values, exact minimizers and approximate minimizers under distribution approximation. It is independent of the proof of the mission's published redistribution goal.
--
--   **Formalization Note** One pair of constants precedes both regimes and every perturbation. The second regime requires only its displayed closeness condition. Hausdorff distance is global and symmetric. The admissible class, extended integrands and exact conditioning modulus are retained. No finite-support, cost-function, Lipschitz, normal-integrand, strong-convexity or uniqueness premise is added. The admissible class imposes the two outer bounds of $\mathcal P_f$ for every radius. It omits the printed middle inequality, which is automatic on nonempty balls and would otherwise empty the class whenever $0\notin X$.
--
--   Differences from the source:
--   - encoding: model (1) on real finite-dimensional spaces with relative Borel probabilities → the published general model at zero stochastic constraints, using Euclidean vectors and measures on the scenario subtype; reason: the data specialize exactly to X, Omega and one extended-real objective; no imported regularity assumptions are imposed
--   - encoding: extended expectations and the exact probability class for every positive radius → positive/negative Lebesgue expectations with EReal bounds and the same integral-of-infimum and supremum-of-integrals ordering; reason: admissibility excludes undefined infinite cancellation; no Bochner zero defaults, finite-support restriction or omitted empty-ball radius occurs
--   - reading: conditioning minimum of model (1) and the notation psi inverse → extended infimum over feasible x and the monotone generalized inverse sup{tau>=0:psi(tau)<=t}; reason: the model includes X, empty conditioning domains have value positive infinity, finite nonempty minima are attained, and no bijectivity is assumed
--   - encoding: the solution inclusion and global distance of nonempty closed approximate-solution sets → existence of a reference minimizer within the closed radius and Mathlib global hausdorffEDist; reason: these agree with the printed enlargement and supremum of point-to-set-distance differences on the theorem regime; containment is non-strict
--   - encoding: real absolute difference of optimal values and Hausdorff distance of nonempty sets → explicit finiteness of the two values in the first regime and explicit nonemptiness of both epsilon-solution sets in the second; reason: these are implicit well-posedness conclusions of the printed formulas, not additional hypotheses or excluded instances
--   - correction: the chain −∞ < ∫ inf f dQ ≤ sup ∫ f dQ < ∞ for each ρ > 0 in P_f → only the two outer bounds for each ρ > 0; reason: the middle inequality is automatic when X∩ρB is nonempty, and on an empty ball it reads +∞ ≤ −∞, which would empty P_f (and make the theorem vacuous) for every X with 0 ∉ X; the source of Theorem 1, [20], states the two bounds separately
-- source:
--   Dupačová, Gröwe-Kuska, Römisch, Scenario reduction in stochastic programming, Math. Program. Ser. A 95 (2003), DOI 10.1007/s10107-002-0331-0, p. 496, Theorem 1 (proof pp. 496–497), PDF 4–5

import Mathlib
import Definitions.Def_ScenarioReduction_Redistribution_Supplement_standing
import Definitions.Def_ScenarioReduction_Redistribution_Supplement_epsilonSolutions
import Definitions.Def_ScenarioReduction_Redistribution_Supplement_admissible
import Definitions.Def_ScenarioReduction_Redistribution_Supplement_informationDistance
import Definitions.Def_ScenarioReduction_Redistribution_Supplement_conditioningModulus
set_option autoImplicit false
open scoped ENNReal

namespace ScenarioReduction.Redistribution.Supplement

/-- Theorem 1, p. 496: both regimes, with the SAME constants. No additional
closeness condition is imposed in the epsilon-solution regime. -/
theorem quantitative_stability {n s : ℕ} (M : ProbMetricStab.General.Model n s 0)
    (hM : standing M) (P : MeasureTheory.Measure M.Ξ) (hP : admissible M P)
    (hS : (M.S P).Nonempty) (hSb : Bornology.IsBounded (M.S P)) :
    ∃ ρ εbar : ℝ, 0 < ρ ∧ 0 < εbar ∧
      (∀ Q : MeasureTheory.Measure M.Ξ, admissible M Q →
        informationDistance M ρ P Q < ENNReal.ofReal εbar →
        (M.v P ≠ ⊤ ∧ M.v P ≠ ⊥ ∧ M.v Q ≠ ⊤ ∧ M.v Q ≠ ⊥ ∧
          EReal.abs (M.v P - M.v Q) ≤ informationDistance M ρ P Q) ∧
        (M.S Q).Nonempty ∧
        ∀ x ∈ M.S Q, ∃ y ∈ M.S P,
          edist x y ≤ conditioningModulus M P (informationDistance M ρ P Q)) ∧
      (∀ ε : ℝ, 0 < ε → ε < εbar →
        ∀ Q : MeasureTheory.Measure M.Ξ, admissible M Q →
          informationDistance M (ρ + ε) P Q < ENNReal.ofReal ε →
          (epsilonSolutions M P ε).Nonempty ∧ (epsilonSolutions M Q ε).Nonempty ∧
          Metric.hausdorffEDist (epsilonSolutions M P ε) (epsilonSolutions M Q ε) ≤
            ENNReal.ofReal (2 * ρ / ε) * informationDistance M (ρ + ε) P Q) := by sorry

end ScenarioReduction.Redistribution.Supplement
