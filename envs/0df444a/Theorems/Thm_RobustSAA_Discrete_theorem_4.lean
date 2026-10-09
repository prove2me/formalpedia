-- Prove2me | Theorems.Thm_RobustSAA_Discrete_theorem_4
-- name    : RobustSAA.Discrete.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:16:47.833994+00:00
-- url     : https://prove2.me/theorems/807b24aa-923f-4f07-b883-912a1accdf90
-- title:
--   Theorem 4, p. 14 — the Pearson χ² and G tests are uniformly consistent
-- statement:
--   On a known finite support of $n$ labels, fix any nonnegative constant $Q$ independent of sample size. At size $N$, accept a hypothetical distribution when its Pearson or G statistic, respectively, does not exceed $\sqrt{Q/N}$. For either test, if the true law is $F$ and $(F_N)$ is any sequence of hypothetical laws that does not converge weakly to $F$, then almost surely $F_N$ is rejected infinitely often. Thus both confidence-region maps are uniformly consistent:
--
--   $$
--   \operatorname{UC}(\mathcal F_N^{\chi^2})\ \land\ \operatorname{UC}(\mathcal F_N^{G}).
--   $$
--
--   This is Theorem 4's statistical condition used by the paper's general convergence characterization for robust sample average approximation.
--
--   **Formalization Note** Support points are represented by labels `Fin n`, and $Q$ is a fixed nonnegative parameter rather than a formalized chi-square quantile; the paper's proof uses only its independence from $N$. The G region compares squared statistics, equivalently comparing $G_N$ with $\sqrt{Q/N}$ for positive $N$.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Theorem 4, p. 14; §10.6 proof p. 38

import Mathlib
import Definitions.Def_RobustSAA_Discrete_Setting

namespace RobustSAA.Discrete

open MeasureTheory

theorem theorem_4 (n : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) :
    IsUniformlyConsistent (chiRegion (n := n) Q) ∧
      IsUniformlyConsistent (gRegion (n := n) Q) := by sorry

end RobustSAA.Discrete
