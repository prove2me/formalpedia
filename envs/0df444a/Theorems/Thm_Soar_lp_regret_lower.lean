-- Prove2me | Theorems.Thm_Soar_lp_regret_lower
-- name    : Soar.lp_regret_lower
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-23T02:44:11.131419+00:00
-- url     : https://prove2.me/theorems/733d05a3-646e-4c0b-b0a9-6a4df24cc51e
-- title:
--   Optimal regret for the -‖x−y‖^p quality function: lower bound (Theorem 2)
-- statement:
--   **Standing conventions of Section 4.** Demand and supply units live in $\mathbb R^d$ with the Euclidean norm, $d \ge 1$; $P$ and $Q$ are probability measures on $\mathbb R^d$; the hindsight optimum $U^H_n$, its limit $U_\infty = \sup_{n \ge 1} U^H_n$ and the regret $\mathrm{Reg}_n(\pi) = U_\infty - U_n(\pi)$ are as in the model bundle; $U_n(\mathrm{SOAR})$ is the average expected match value of SOAR run with a measurable optimal offline solver, and $U_n(\pi)$ that of a dynamic matching policy $\pi$ (a non-anticipative, possibly randomized assignment rule). All constants $C$, $c$ may depend on the instance $(P, Q, d, p)$ but not on $n$.
--
--   Fix $p \ge 1$ and the quality function $\varphi_p(x, y) = -\|x - y\|^p$. Then there exist demand and supply distributions $P$ and $Q$ on $\mathbb R^d$ supported on bounded sets, a constant $c = c(P, Q, d, p) > 0$ and an $n_0$ such that for every $n \ge n_0$ and every dynamic matching policy $\pi$,
--   $$\mathrm{Reg}_n(\pi) \ge \begin{cases} c\, n^{-1/2}, & d \le 2(p \wedge 2),\\ c\, n^{-(p \wedge 2)/d}, & d > 2(p \wedge 2); \end{cases}$$
--   that is, $\inf_{\pi \in \Pi} \mathrm{Reg}_n(\pi)$ is bounded below by the right-hand side.
--
--   **Role.** This is the second half of Theorem 2, which the paper phrases as "the aforementioned regret scaling is nearly the best possible": together with the upper bound it establishes the near-optimality of SOAR among all dynamic matching policies, the gap being only the $\log n$ factor in the critical dimension $d = 2(p \wedge 2)$.
--
--   **Formalization Note** The policy class is the class of non-anticipative measurable assignment rules with an arbitrary seed space, quantified after the instance and the constant, as in $\inf_{\pi \in \Pi}$. The two cases are the function $r^{\downarrow}_{d,p}(n)$ of the Euclidean bundle; the paper lists $d < 2(p\wedge 2)$ and $d = 2(p \wedge 2)$ separately with the same rate $n^{-1/2}$. The paper's display carries no quantifier on $n$; the proof in Appendix H is asymptotic (it invokes the central limit theorem), so the statement is made for all $n \ge n_0$. The hard instance is existential, so the constant may depend on it.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 4.1, Theorem 2 (lower bound), and Appendix H

import Mathlib
import Definitions.Def_SoarPolicies
import Definitions.Def_SoarEuclidean

open MeasureTheory

universe u

namespace Soar

theorem lp_regret_lower (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 1 ≤ p) :
    ∃ (P Q : Measure (EuclideanSpace ℝ (Fin d))) (_ : IsProbabilityMeasure P)
      (_ : IsProbabilityMeasure Q), SoarBoundedSupport P ∧ SoarBoundedSupport Q ∧
      ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (π : SoarDynamicPolicy (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) Ω n),
          c * SoarRateLpLower d p n ≤ SoarPolicyRegret P Q μ (SoarLpQuality d p) π := by
  sorry

end Soar
