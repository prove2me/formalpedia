-- Prove2me | Theorems.Thm_Soar_dot_regret_upper
-- name    : Soar.dot_regret_upper
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-23T02:45:48.004547+00:00
-- url     : https://prove2.me/theorems/730f3ea6-d041-4fd1-9427-ebf5f326a849
-- title:
--   Regret of SOAR for the dot-product quality function: upper bound (Corollary 3)
-- statement:
--   **Standing conventions of Section 4.** Demand and supply units live in $\mathbb R^d$ with the Euclidean norm, $d \ge 1$; $P$ and $Q$ are probability measures on $\mathbb R^d$; the hindsight optimum $U^H_n$, its limit $U_\infty = \sup_{n \ge 1} U^H_n$ and the regret $\mathrm{Reg}_n(\pi) = U_\infty - U_n(\pi)$ are as in the model bundle; $U_n(\mathrm{SOAR})$ is the average expected match value of SOAR run with a measurable optimal offline solver, and $U_n(\pi)$ that of a dynamic matching policy $\pi$ (a non-anticipative, possibly randomized assignment rule). All constants $C$, $c$ may depend on the instance $(P, Q, d, p)$ but not on $n$.
--
--   Suppose $P$ and $Q$ are supported on bounded sets, and let the quality function be the dot product $\varphi(x, y) = \langle x, y \rangle$. Then there is a constant $C = C(P, Q, d) < \infty$ such that for every $n \ge 2$,
--   $$\mathrm{Reg}_n(\mathrm{SOAR}) \le \begin{cases} C\, n^{-1/2}, & d < 4,\\ C\, n^{-1/2} \log n, & d = 4,\\ C\, n^{-2/d}, & d > 4, \end{cases}$$
--   the upper bound of Theorem 2 with $p = 2$.
--
--   **Role.** Corollary 3 transfers Theorem 2 to the dot-product quality function, the case motivated by recommender systems; via the augmentation of Remark 6 it also covers scarce supply with rejection cost, and via Remark 7 polynomial kernel qualities. Together with Theorem 3 it gives the paper's guarantees for $\langle x, y\rangle$.
--
--   **Formalization Note** The rate is $r^{\uparrow}_{d,2}(n)$ of the Euclidean bundle. Regret is defined directly for the dot-product quality (the benchmark $U_\infty$ is computed for $\langle x, y\rangle$); the equivalence with $\varphi_2$ of Lemma G.7 is part of the proof, not of the statement. As in Theorem 2, the bound starts at $n \ge 2$ because of the $\log n$ in the critical dimension $d = 4$.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 4.2, Corollary 3 (with Theorem 2, $p = 2$, and Lemma G.7)

import Mathlib
import Definitions.Def_SoarPolicy
import Definitions.Def_SoarEuclidean

open MeasureTheory

namespace Soar

theorem dot_regret_upper (d : ℕ) (hd : 1 ≤ d)
    (P Q : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : SoarBoundedSupport P) (hQ : SoarBoundedSupport Q)
    (opt : (m : ℕ) → (Fin m → EuclideanSpace ℝ (Fin d)) → (Fin m → EuclideanSpace ℝ (Fin d)) →
      Equiv.Perm (Fin m))
    (hsolver : SoarIsSolver (SoarDotQuality d) opt) (hopt : SoarSolverMeasurable opt) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      SoarRegret P Q (SoarDotQuality d) opt n ≤ C * SoarRateLp d 2 n := by
  sorry

end Soar
