-- Prove2me | Theorems.Thm_Soar_uniform_regret_upper
-- name    : Soar.uniform_regret_upper
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-23T02:44:40.143924+00:00
-- url     : https://prove2.me/theorems/1ab65db8-58d8-4a52-85f7-d8c8ff8eca3b
-- title:
--   Sharper regret of SOAR for uniform demand and supply: upper bound (Proposition 2)
-- statement:
--   **Standing conventions of Section 4.** Demand and supply units live in $\mathbb R^d$ with the Euclidean norm, $d \ge 1$; $P$ and $Q$ are probability measures on $\mathbb R^d$; the hindsight optimum $U^H_n$, its limit $U_\infty = \sup_{n \ge 1} U^H_n$ and the regret $\mathrm{Reg}_n(\pi) = U_\infty - U_n(\pi)$ are as in the model bundle; $U_n(\mathrm{SOAR})$ is the average expected match value of SOAR run with a measurable optimal offline solver, and $U_n(\pi)$ that of a dynamic matching policy $\pi$ (a non-anticipative, possibly randomized assignment rule). All constants $C$, $c$ may depend on the instance $(P, Q, d, p)$ but not on $n$.
--
--   Suppose $P = Q = \mathrm{Uniform}([0,1]^d)$ and let the quality function be $\varphi_p(x, y) = -\|x - y\|^p$ for some $p \ge 1$. Then there is a constant $C = C(d, p) < \infty$ such that for every $n \ge 2$, $\mathrm{Reg}_n(\mathrm{SOAR}) \le C\, u_{d,p}(n)$ where
--   $$u_{d,p}(n) = \begin{cases} n^{-(\frac p2 \wedge 1)}\,\mathbf 1\{p \ne 2\} + n^{-1}\log n\,\mathbf 1\{p = 2\}, & d = 1,\\[2pt] (n^{-1}\log n)^{p/2}\,\mathbf 1\{p < 2\} + n^{-1}(\log n)^2\,\mathbf 1\{p = 2\} + n^{-1}\,\mathbf 1\{p > 2\}, & d = 2,\\[2pt] n^{-(\frac pd \wedge 1)}\,\mathbf 1\{p \ne d\} + n^{-1}\log n\,\mathbf 1\{p = d\}, & d \ge 3. \end{cases}$$
--
--   **Role.** This is the upper bound of Proposition 2: for the smooth, identical distributions $P = Q = \mathrm{Uniform}([0,1]^d)$ the regret of SOAR improves on Theorem 2 in several regimes, e.g. from $\Theta(n^{-2/d})$ to $\tilde\Theta(n^{-p/d})$ for $p \in (2, d]$ and $d \ge 4$. As the paper notes, this resolves the open problem posed in Kanoria (2022) for $\varphi_p$ with $d \ge 2$ and $p \le d$.
--
--   **Formalization Note** $\mathrm{Uniform}([0,1]^d)$ is Lebesgue measure restricted to the cube $\{x : 0 \le x_i \le 1\}$, whose total mass $1$ is proved in the Euclidean bundle. The table is the function $u_{d,p}(n)$ of that bundle, with the indicator sums written as case distinctions. The bound starts at $n \ge 2$ because several entries contain $\log n$. The solver is any measurable optimal offline solver.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 4.1, Proposition 2 (upper bound), and Appendix I

import Mathlib
import Definitions.Def_SoarPolicy
import Definitions.Def_SoarEuclidean

open MeasureTheory

namespace Soar

theorem uniform_regret_upper (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 1 ≤ p)
    (opt : (m : ℕ) → (Fin m → EuclideanSpace ℝ (Fin d)) → (Fin m → EuclideanSpace ℝ (Fin d)) →
      Equiv.Perm (Fin m))
    (hsolver : SoarIsSolver (SoarLpQuality d p) opt) (hopt : SoarSolverMeasurable opt) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      SoarRegret (SoarUniformCube d) (SoarUniformCube d) (SoarLpQuality d p) opt n
        ≤ C * SoarRateUniform d p n := by
  sorry

end Soar
