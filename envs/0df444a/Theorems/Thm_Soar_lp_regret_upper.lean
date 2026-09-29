-- Prove2me | Theorems.Thm_Soar_lp_regret_upper
-- name    : Soar.lp_regret_upper
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-23T02:43:21.246789+00:00
-- url     : https://prove2.me/theorems/26f54c95-076f-44f7-97f2-1f597bcf0c7b
-- title:
--   Regret of SOAR for the -‖x−y‖^p quality function: upper bound (Theorem 2)
-- statement:
--   **Standing conventions of Section 4.** Demand and supply units live in $\mathbb R^d$ with the Euclidean norm, $d \ge 1$; $P$ and $Q$ are probability measures on $\mathbb R^d$; the hindsight optimum $U^H_n$, its limit $U_\infty = \sup_{n \ge 1} U^H_n$ and the regret $\mathrm{Reg}_n(\pi) = U_\infty - U_n(\pi)$ are as in the model bundle; $U_n(\mathrm{SOAR})$ is the average expected match value of SOAR run with a measurable optimal offline solver, and $U_n(\pi)$ that of a dynamic matching policy $\pi$ (a non-anticipative, possibly randomized assignment rule). All constants $C$, $c$ may depend on the instance $(P, Q, d, p)$ but not on $n$.
--
--   Suppose $P$ and $Q$ are supported on bounded sets, and let the quality function be $\varphi_p(x, y) = -\|x - y\|^p$ for some $p \ge 1$. Then there is a constant $C = C(P, Q, d, p) < \infty$ such that for every $n \ge 2$,
--   $$\mathrm{Reg}_n(\mathrm{SOAR}) \le \begin{cases} C\, n^{-1/2}, & d < 2(p \wedge 2),\\ C\, n^{-1/2} \log n, & d = 2(p \wedge 2),\\ C\, n^{-(p \wedge 2)/d}, & d > 2(p \wedge 2). \end{cases}$$
--
--   **Role.** This is the upper bound of Theorem 2, the paper's main regret guarantee for general distributions: SOAR achieves the rate of the empirical optimal transport problem, which Theorem 2's lower bound shows is the best possible up to the logarithmic factor in the critical dimension. Its two important special cases are $p = 1$ (the Euclidean distance cost of Kanoria 2022) and $p = 2$ (equivalent to the dot-product quality, Corollary 3).
--
--   **Formalization Note** The three cases are the function $r^{\uparrow}_{d,p}(n)$ of the Euclidean bundle. The bound is stated for $n \ge 2$ because the rate in the critical dimension contains $\log n$, which vanishes at $n = 1$ while the regret there is $U_\infty - U^H_1$, generally positive; for the other cases the restriction is immaterial since $C$ is existential. The solver is any measurable optimal offline solver, as in Theorem 1. The quality function $\varphi_p$ is unbounded on $\mathbb R^d$; boundedness of the supports of $P$ and $Q$ is what the paper assumes and what makes all expectations finite, so no global bound on $\varphi_p$ is imposed.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 4.1, Theorem 2 (upper bound), and Appendix H

import Mathlib
import Definitions.Def_SoarPolicy
import Definitions.Def_SoarEuclidean

open MeasureTheory

namespace Soar

theorem lp_regret_upper (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 1 ≤ p)
    (P Q : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : SoarBoundedSupport P) (hQ : SoarBoundedSupport Q)
    (opt : (m : ℕ) → (Fin m → EuclideanSpace ℝ (Fin d)) → (Fin m → EuclideanSpace ℝ (Fin d)) →
      Equiv.Perm (Fin m))
    (hsolver : SoarIsSolver (SoarLpQuality d p) opt) (hopt : SoarSolverMeasurable opt) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      SoarRegret P Q (SoarLpQuality d p) opt n ≤ C * SoarRateLp d p n := by
  sorry

end Soar
