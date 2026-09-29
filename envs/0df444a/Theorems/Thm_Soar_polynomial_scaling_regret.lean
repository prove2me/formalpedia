-- Prove2me | Theorems.Thm_Soar_polynomial_scaling_regret
-- name    : Soar.polynomial_scaling_regret
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-23T02:41:35.623209+00:00
-- url     : https://prove2.me/theorems/95600303-1ff8-4e2c-af02-88549bb014f5
-- title:
--   Tight regret scaling of SOAR under polynomial scaling (Corollary 2, second part)
-- statement:
--   **Standing conventions.** Throughout, $\mathcal X$ (demand weight vectors) and $\mathcal Y$ (supply feature vectors) are measurable spaces, $P$ and $Q$ are probability measures on them, and the match quality function $\varphi : \mathcal X \times \mathcal Y \to \mathbb R$ is jointly measurable and bounded, $|\varphi(x,y)| \le C$ for all $x, y$. Expectations over $n$ i.i.d. demand units and $n$ independent i.i.d. supply units are integrals against the product measure $P^{\otimes n} \otimes Q^{\otimes n}$ on $\mathcal X^n \times \mathcal Y^n$. The hindsight optimum value is
--   $$U^H_n = \frac{1}{n}\,\mathbb E\Bigl[\sup_{\sigma \in S_n} \sum_{t=1}^{n} \varphi\bigl(X_t, Y_{\sigma(t)}\bigr)\Bigr],$$
--   with $S_n$ the symmetric group, and the limiting hindsight optimum is $U_\infty = \sup_{n \ge 1} U^H_n$.
--
--   Let $\mathrm{opt}$ be a measurable offline assignment solver for $\varphi$, and write $\mathrm{Reg}_n(\mathrm{SOAR}) = U_\infty - U_n(\mathrm{SOAR})$ and $\mathrm{Reg}_n(\mathrm{H\text{-}OPT}) = U_\infty - U^H_n$. Suppose the matching instance $(P, Q, \varphi)$ scales polynomially with parameter $\beta$ and limit $l_0$, that is, it scales regularly with parameter $\beta > 0$ and $n^{\beta}\,\mathrm{Reg}_n(\mathrm{H\text{-}OPT}) \to l_0$, and suppose $l_0 > 0$. Then all four of the following hold.
--
--   1. If $\beta < 1$, there is a constant $l_1$ such that $\mathrm{Reg}_n(\mathrm{SOAR}) \le l_1\,\mathrm{Reg}_n(\mathrm{H\text{-}OPT})$ for every $n \ge 1$.
--   2. If $\beta = 1$, there is a constant $l_1$ such that $\mathrm{Reg}_n(\mathrm{SOAR}) \le l_1 \log n \cdot \mathrm{Reg}_n(\mathrm{H\text{-}OPT})$ for every $n \ge 2$.
--   3. If $\beta < 1$, there are constants $c_1 > 0$ and $c_2$ such that for every $n \ge 1$,
--   $$c_1\, n^{-\beta} \le \mathrm{Reg}_n(\mathrm{SOAR}) \le c_2\, n^{-\beta}, \qquad\text{i.e. } \mathrm{Reg}_n(\mathrm{SOAR}) = \Theta(n^{-\beta}).$$
--   4. If $\beta = 1$, there are constants $c_1 > 0$ and $c_2$ such that for every $n \ge 2$,
--   $$c_1\, \frac{\log n}{n} \le \mathrm{Reg}_n(\mathrm{SOAR}) \le c_2\, \frac{\log n}{n}, \qquad\text{i.e. } \mathrm{Reg}_n(\mathrm{SOAR}) = \Theta(n^{-1} \log n).$$
--
--   **Role.** This is the second half of Corollary 2, the paper's tight characterization of the regret scaling of SOAR: under polynomial scaling of the hindsight regret, SOAR attains the optimal regret scaling up to at most a logarithmic factor, since by Appendix A no policy has smaller regret than the hindsight-optimal algorithm. Via Remark 4 it is elementary analysis of the Cesàro average of a sequence asymptotic to $l_0 k^{-\beta}$.
--
--   **Formalization Note** Three points are made explicit that the source leaves implicit. First, the limit $l_0$ must be positive: with $l_0 = 0$ the hindsight regret can drop abruptly between consecutive blocks of indices while still satisfying regular scaling, and then the ratio $\mathrm{Reg}_n(\mathrm{SOAR}) / \mathrm{Reg}_n(\mathrm{H\text{-}OPT})$ is unbounded, so conclusions 1–4 fail; the paper's proof uses $l_0 - \delta > 0$. Second, the $\beta = 1$ bounds are stated for $n \ge 2$ because $\log 1 = 0$ while $\mathrm{Reg}_1(\mathrm{SOAR}) = \mathrm{Reg}_1(\mathrm{H\text{-}OPT}) > 0$; the paper writes "for all $n \in \mathbb N$". Third, the paper's statement lists the cases $\beta \in (0,1)$ and $\beta = 1$ only, relying on its Appendix D claim that $\beta \le 1$; the formalization states exactly those two cases, so it makes no claim for $\beta > 1$. The constants $l_1, c_1, c_2$ may depend on $(P, Q, \varphi)$ and the solver but not on $n$. The powers are real powers of the real number $n$ and $\log$ is the natural logarithm.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 3.2.2, Corollary 2 (second and third displays), and Appendix D, 'Polynomial Regret Scaling Case'

import Mathlib
import Definitions.Def_SoarPolicy
import Definitions.Def_SoarScaling

open MeasureTheory Filter Topology

namespace Soar

theorem polynomial_scaling_regret {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hsolver : SoarIsSolver φ opt) (hopt : SoarSolverMeasurable opt)
    (β l₀ : ℝ) (hpoly : SoarScalesPolynomially P Q φ β l₀) (hl₀ : 0 < l₀) :
    (β < 1 → ∃ l₁ : ℝ, ∀ n : ℕ, 1 ≤ n →
        SoarRegret P Q φ opt n ≤ l₁ * SoarRegretH P Q φ n) ∧
    (β = 1 → ∃ l₁ : ℝ, ∀ n : ℕ, 2 ≤ n →
        SoarRegret P Q φ opt n ≤ l₁ * Real.log n * SoarRegretH P Q φ n) ∧
    (β < 1 → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ n : ℕ, 1 ≤ n →
        c₁ * (n : ℝ) ^ (-β) ≤ SoarRegret P Q φ opt n ∧
          SoarRegret P Q φ opt n ≤ c₂ * (n : ℝ) ^ (-β)) ∧
    (β = 1 → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ n : ℕ, 2 ≤ n →
        c₁ * Real.log n / n ≤ SoarRegret P Q φ opt n ∧
          SoarRegret P Q φ opt n ≤ c₂ * Real.log n / n) := by
  sorry

end Soar
