-- Prove2me | Theorems.Thm_Soar_hindsight_abs_le
-- name    : Soar.hindsight_abs_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-22T18:58:00.689199+00:00
-- url     : https://prove2.me/theorems/7ef920ee-c2a9-494f-ab57-6e9e5bac3990
-- title:
--   The hindsight benchmark is bounded
-- statement:
--   **Standing conventions.** Throughout, $\mathcal X$ (demand weight vectors) and $\mathcal Y$ (supply feature vectors) are measurable spaces, $P$ and $Q$ are probability measures on them, and the match quality function $\varphi : \mathcal X \times \mathcal Y \to \mathbb R$ is jointly measurable and bounded, $|\varphi(x,y)| \le C$ for all $x, y$. Expectations over $n$ i.i.d. demand units and $n$ independent i.i.d. supply units are integrals against the product measure $P^{\otimes n} \otimes Q^{\otimes n}$ on $\mathcal X^n \times \mathcal Y^n$. The hindsight optimum value is
--   $$U^H_n = \frac{1}{n}\,\mathbb E\Bigl[\sup_{\sigma \in S_n} \sum_{t=1}^{n} \varphi\bigl(X_t, Y_{\sigma(t)}\bigr)\Bigr],$$
--   with $S_n$ the symmetric group, and the limiting hindsight optimum is $U_\infty = \sup_{n \ge 1} U^H_n$.
--
--   Then every hindsight optimum value and the limiting hindsight optimum are bounded by the same constant:
--   $$|U^H_n| \le C \quad \text{for all } n, \qquad\text{and}\qquad |U_\infty| \le C .$$
--
--   **Role.** The paper assumes $\varphi$ bounded precisely so that $U^H_n$ and $U_\infty$ are finite and the regret is well defined; this is the statement "with bounded quality function $\varphi$, $U^H_n$ are trivially bounded, then by monotone convergence $U_\infty$ is also bounded" of Appendix A.
--
--   **Formalization Note** The bound for $n = 0$ holds because $U^H_0$ is the junk value $0$ and $C \ge 0$ (a probability measure on $\mathcal X$ forces $\mathcal X$ nonempty, so some $|\varphi(x,y)| \le C$ exists). The bound on $U_\infty = \sup_{n \ge 1} U^H_n$ needs no monotonicity: a supremum of a sequence bounded in absolute value by $C$ is bounded by $C$.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 2 and Appendix A (boundedness of $U^H_n$ and $U_\infty$)

import Mathlib
import Definitions.Def_SoarModel

open MeasureTheory

namespace Soar

theorem hindsight_abs_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C) :
    (∀ n : ℕ, |SoarHindsight P Q φ n| ≤ C) ∧ |SoarLimit P Q φ| ≤ C := by
  sorry

end Soar
