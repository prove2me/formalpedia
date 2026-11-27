-- Prove2me | Theorems.Thm_ScenarioApproach_EmpiricalCosts_uniform_kthLargest_joint_cdf
-- name    : ScenarioApproach.EmpiricalCosts.uniform_kthLargest_joint_cdf
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T06:49:57.019198+00:00
-- url     : https://prove2.me/theorems/15bfe127-6e0e-406a-bc09-8ce2046bdfd1
-- title:
--   Order statistics of uniform samples follow the ordered Dirichlet law $(d,1,\dots,1)$
-- statement:
--   Let $u_1,\dots,u_N$ be independent random variables, each uniformly distributed on $[0,1]$, and let $U_{[k]}$ denote the $k$-th largest of them ($U_{[1]}\ge U_{[2]}\ge\cdots\ge U_{[N]}$). Equivalently, $W_{(k)}=1-U_{[k]}$ is the $k$-th smallest of the uniform variables $1-u_1,\dots,1-u_N$. For $1\le d\le N$ and all real numbers $\varepsilon_d,\dots,\varepsilon_N$,
--
--   $$
--   \mathbb P\{1-U_{[d]}\le\varepsilon_d,\ \dots,\ 1-U_{[N]}\le\varepsilon_N\}=\frac{N!}{(d-1)!}\int_0^{\varepsilon_d}\alpha_d^{d-1}\int_0^{\varepsilon_{d+1}}\!\!\cdots\int_0^{\varepsilon_N}\mathbf 1_{\{0\le\alpha_d\le\cdots\le\alpha_N\le1\}}\,\mathrm d\alpha_N\cdots\mathrm d\alpha_d .
--   $$
--
--   That is, the order statistics $(W_{(d)},\dots,W_{(N)})$ of $N$ independent uniform variables have the ordered Dirichlet distribution with parameters $(d,1,\dots,1)$, the law appearing in Theorem 8.4 of Campi and Garatti. In the scenario approach this is the case of a cost that does not depend on the decision: it is the reference law to which the risks of the empirical costs of every nondegenerate scenario program are equal in distribution.
--
--   **Formalization Note** The right-hand side is `orderedDirichletCDF d N ε`, a Lebesgue integral over the box $\prod_k[0,\varepsilon_k]$ intersected with the ordered simplex; the uniform law is Lebesgue measure restricted to $[0,1]$ and the sample law is the product measure.
-- source:
--   Reference law in M. C. Campi, S. Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, doi:10.1137/1.9781611975444, Chapter 8, Sec. 8.1, p. 90, Theorem 8.4 (stated without proof); A. Carè, S. Garatti, M. C. Campi, Scenario min-max optimization and the risk of empirical costs, SIAM J. Optim. 25(4):2061-2080, 2015, doi:10.1137/130928546. Joint density $N!$ of the order statistics of $N$ i.i.d. uniforms: H. A. David, H. N. Nagaraja, Order Statistics, 3rd ed., Wiley 2003, Section 2.2.

import Mathlib
import Definitions.Def_ScenarioApproach_EmpiricalCosts_empiricalCost
import Definitions.Def_ScenarioApproach_EmpiricalCosts_orderedDirichletCDF
namespace ScenarioApproach.EmpiricalCosts

/-- Joint distribution function of the order statistics of `N` i.i.d. uniform variables on
`[0,1]`: with `U_[k]` the `k`-th largest of `u 0, …, u (N-1)`, the vector
`(1 - U_[d], …, 1 - U_[N])` (the `d`-th, …, `N`-th smallest of `1 - u`) has the ordered Dirichlet
distribution with parameters `(d, 1, …, 1)`, for `1 ≤ d ≤ N` and all real `ε_d, …, ε_N`. -/
theorem uniform_kthLargest_joint_cdf {d N : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N) (ε : ℕ → ℝ) :
    MeasureTheory.Measure.pi
        (fun _ : Fin N => (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc 0 1))
        {u | ∀ k : ℕ, d ≤ k → k ≤ N → 1 - kthLargest u k ≤ ε k} =
      ENNReal.ofReal (orderedDirichletCDF d N ε) := by sorry

end ScenarioApproach.EmpiricalCosts
