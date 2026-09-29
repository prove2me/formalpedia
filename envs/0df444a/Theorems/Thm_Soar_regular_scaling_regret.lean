-- Prove2me | Theorems.Thm_Soar_regular_scaling_regret
-- name    : Soar.regular_scaling_regret
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-22T19:03:39.154449+00:00
-- url     : https://prove2.me/theorems/c435af72-2b3c-4e9d-b772-584e9f16c29a
-- title:
--   Regret scaling of SOAR under regular scaling (Corollary 2, first part)
-- statement:
--   **Standing conventions.** Throughout, $\mathcal X$ (demand weight vectors) and $\mathcal Y$ (supply feature vectors) are measurable spaces, $P$ and $Q$ are probability measures on them, and the match quality function $\varphi : \mathcal X \times \mathcal Y \to \mathbb R$ is jointly measurable and bounded, $|\varphi(x,y)| \le C$ for all $x, y$. Expectations over $n$ i.i.d. demand units and $n$ independent i.i.d. supply units are integrals against the product measure $P^{\otimes n} \otimes Q^{\otimes n}$ on $\mathcal X^n \times \mathcal Y^n$. The hindsight optimum value is
--   $$U^H_n = \frac{1}{n}\,\mathbb E\Bigl[\sup_{\sigma \in S_n} \sum_{t=1}^{n} \varphi\bigl(X_t, Y_{\sigma(t)}\bigr)\Bigr],$$
--   with $S_n$ the symmetric group, and the limiting hindsight optimum is $U_\infty = \sup_{n \ge 1} U^H_n$.
--
--   Let $\mathrm{opt}$ be a measurable offline assignment solver for $\varphi$, and write $\mathrm{Reg}_n(\mathrm{SOAR}) = U_\infty - U_n(\mathrm{SOAR})$ and $\mathrm{Reg}_n(\mathrm{H\text{-}OPT}) = U_\infty - U^H_n$. Suppose the matching instance $(P, Q, \varphi)$ scales regularly with parameter $\beta$, where $0 < \beta \le 1$: for every $0 < \epsilon' < \beta$, $n^{\beta - \epsilon'} \mathrm{Reg}_n(\mathrm{H\text{-}OPT}) \to 0$ and $n^{\beta + \epsilon'} \mathrm{Reg}_n(\mathrm{H\text{-}OPT}) \to \infty$. Then for every $\epsilon > 0$,
--   $$\lim_{n \to \infty} n^{\beta - \epsilon}\,\mathrm{Reg}_n(\mathrm{SOAR}) = 0, \qquad \lim_{n \to \infty} n^{\beta + \epsilon}\,\mathrm{Reg}_n(\mathrm{SOAR}) = \infty,$$
--   and
--   $$\mathrm{Reg}_n(\mathrm{SOAR}) \le n^{\epsilon}\,\mathrm{Reg}_n(\mathrm{H\text{-}OPT}) \qquad \text{for all sufficiently large } n .$$
--
--   **Role.** This is the first half of Corollary 2: under regular scaling SOAR's regret has the same polynomial exponent as the hindsight regret, and no policy can beat the hindsight regret, so SOAR is near-optimal up to a factor $n^{\epsilon}$. The paper's examples are the uniform instances on $[0,1]^d$ with $\varphi = -\|x-y\|^p$, whose hindsight regrets scale regularly by the results of Caracciolo et al.
--
--   **Formalization Note** The paper states the corollary for every $\beta > 0$ and, in Appendix D, first argues that $\beta \le 1$ necessarily holds, on the ground that the cumulative hindsight regret $n\,\mathrm{Reg}_n(\mathrm{H\text{-}OPT})$ is bounded below by a positive constant. That lower bound is asserted, not proved, and is not among the paper's assumptions; the formalization therefore takes $\beta \le 1$ as an explicit hypothesis, which is exactly what the asserted bound would give, and which is what the first and third conclusions need (since $\mathrm{Reg}_n(\mathrm{SOAR}) \ge \frac1n \mathrm{Reg}_1(\mathrm{H\text{-}OPT})$ with $\mathrm{Reg}_1(\mathrm{H\text{-}OPT}) > 0$ under regular scaling, they fail for $\beta > 1$). The second conclusion holds for every $\beta > 0$. The paper phrases the first two conclusions with $\limsup$ and $\liminf$; for nonnegative sequences these coincide with the limits. In the third conclusion the paper's Appendix D argument combines an $O(n^{-\beta+\epsilon})$ upper bound with an $n^{-\beta-\epsilon}$ lower bound at the same $\epsilon$, which does not close; it closes with the auxiliary exponent $\epsilon/3$ in both bounds, and the statement is unchanged. The powers are real powers of the real number $n$.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 3.2.2, Corollary 2 (first paragraph), and Appendix D, parts 1)–3)

import Mathlib
import Definitions.Def_SoarPolicy
import Definitions.Def_SoarScaling

open MeasureTheory Filter Topology

namespace Soar

theorem regular_scaling_regret {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hsolver : SoarIsSolver φ opt) (hopt : SoarSolverMeasurable opt)
    (β : ℝ) (hβ : β ≤ 1) (hreg : SoarScalesRegularly P Q φ β) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (β - ε) * SoarRegret P Q φ opt n) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (n : ℝ) ^ (β + ε) * SoarRegret P Q φ opt n) atTop atTop ∧
    ∀ᶠ n : ℕ in atTop, SoarRegret P Q φ opt n ≤ (n : ℝ) ^ ε * SoarRegretH P Q φ n := by
  sorry

end Soar
