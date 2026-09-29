-- Prove2me | Theorems.Thm_Soar_uniform_regret_lower
-- name    : Soar.uniform_regret_lower
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-23T02:45:15.553502+00:00
-- url     : https://prove2.me/theorems/b92d5363-17d5-46ce-83b8-692b0c1e9c6e
-- title:
--   Optimal regret for uniform demand and supply: lower bound (Proposition 2)
-- statement:
--   **Standing conventions of Section 4.** Demand and supply units live in $\mathbb R^d$ with the Euclidean norm, $d \ge 1$; $P$ and $Q$ are probability measures on $\mathbb R^d$; the hindsight optimum $U^H_n$, its limit $U_\infty = \sup_{n \ge 1} U^H_n$ and the regret $\mathrm{Reg}_n(\pi) = U_\infty - U_n(\pi)$ are as in the model bundle; $U_n(\mathrm{SOAR})$ is the average expected match value of SOAR run with a measurable optimal offline solver, and $U_n(\pi)$ that of a dynamic matching policy $\pi$ (a non-anticipative, possibly randomized assignment rule). All constants $C$, $c$ may depend on the instance $(P, Q, d, p)$ but not on $n$.
--
--   Suppose $P = Q = \mathrm{Uniform}([0,1]^d)$ and let the quality function be $\varphi_p(x, y) = -\|x - y\|^p$ for some $p \ge 1$. Then there are a constant $c = c(d, p) > 0$ and an $n_0$ such that for every $n \ge n_0$ and every dynamic matching policy $\pi$, $\mathrm{Reg}_n(\pi) \ge c\, \ell_{d,p}(n)$ where
--   $$\ell_{d,p}(n) = \begin{cases} n^{-(\frac p2 \wedge 1)}\,\mathbf 1\{p \ne 2\} + n^{-1}\,\mathbf 1\{p = 2\}, & d = 1,\\[2pt] (n^{-1}\log n)^{p/2}\,\mathbf 1\{p < 2\} + n^{-1}\log n\,\mathbf 1\{p = 2\} + n^{-1}\,\mathbf 1\{p > 2\}, & d = 2,\\[2pt] n^{-(\frac pd \wedge 1)}\,\mathbf 1\{p \ne d\} + n^{-1}\log n\,\mathbf 1\{p = d\}, & d \ge 3; \end{cases}$$
--   that is, $\inf_{\pi \in \Pi} \mathrm{Reg}_n(\pi) \ge c\,\ell_{d,p}(n)$.
--
--   **Role.** This is the lower bound of Proposition 2, "the aforementioned regret scaling can not be improved in general": for uniform demand and supply the rates achieved by SOAR are optimal among all dynamic matching policies, up to a logarithmic factor at $p = 2$ in dimensions $1$ and $2$. For $p = 2$ it is also the lower bound the paper invokes for Theorem 3.
--
--   **Formalization Note** The table is the function $\ell_{d,p}(n)$ of the Euclidean bundle. The paper writes the constant as $c(d)$; the formal constant may depend on $d$ and on the fixed $p$. The policy class and the asymptotic quantifier $n \ge n_0$ are as in the lower bound of Theorem 2; the proof in Appendix I is asymptotic.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 4.1, Proposition 2 (lower bound), and Appendix I

import Mathlib
import Definitions.Def_SoarPolicies
import Definitions.Def_SoarEuclidean

open MeasureTheory

universe u

namespace Soar

theorem uniform_regret_lower (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 1 ≤ p) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (π : SoarDynamicPolicy (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) Ω n),
        c * SoarRateUniformLower d p n
          ≤ SoarPolicyRegret (SoarUniformCube d) (SoarUniformCube d) μ (SoarLpQuality d p) π := by
  sorry

end Soar
