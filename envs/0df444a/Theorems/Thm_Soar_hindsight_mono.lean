-- Prove2me | Theorems.Thm_Soar_hindsight_mono
-- name    : Soar.hindsight_mono
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-22T18:58:47.485247+00:00
-- url     : https://prove2.me/theorems/677d3aba-7032-4b6a-8f3d-2f88bbfe1d71
-- title:
--   Monotonicity of the hindsight optimum values (Lemma A.1)
-- statement:
--   **Standing conventions.** Throughout, $\mathcal X$ (demand weight vectors) and $\mathcal Y$ (supply feature vectors) are measurable spaces, $P$ and $Q$ are probability measures on them, and the match quality function $\varphi : \mathcal X \times \mathcal Y \to \mathbb R$ is jointly measurable and bounded, $|\varphi(x,y)| \le C$ for all $x, y$. Expectations over $n$ i.i.d. demand units and $n$ independent i.i.d. supply units are integrals against the product measure $P^{\otimes n} \otimes Q^{\otimes n}$ on $\mathcal X^n \times \mathcal Y^n$. The hindsight optimum value is
--   $$U^H_n = \frac{1}{n}\,\mathbb E\Bigl[\sup_{\sigma \in S_n} \sum_{t=1}^{n} \varphi\bigl(X_t, Y_{\sigma(t)}\bigr)\Bigr],$$
--   with $S_n$ the symmetric group, and the limiting hindsight optimum is $U_\infty = \sup_{n \ge 1} U^H_n$.
--
--   Then the hindsight optimum values form a monotone increasing sequence:
--   $$U^H_n \le U^H_{n+1} \qquad \text{for every } n \ge 1 .$$
--
--   **Role.** Lemma A.1 is what makes the limiting hindsight optimum a valid benchmark: with boundedness it gives the existence of $U_\infty = \lim_n U^H_n$ and the inequality $U^H_n \le U_\infty$ used in the definition of regret, and in Corollary 1 it gives that the hindsight regrets $\mathrm{Reg}_k(\mathrm{H\text{-}OPT})$ decrease to $0$. The paper's argument couples the $n$-unit and $(n+1)$-unit problems by removing, from an optimal assignment of $n + 1$ units, the supply unit matched to one designated demand unit; since that supply unit's index is uniform and independent of the supply features, the $n$ units left over are i.i.d. $Q$.
--
--   **Formalization Note** The restriction to $n \ge 1$ excludes the junk value $U^H_0 = 0$, which need not lie below $U^H_1 = \mathbb E[\varphi(X, Y)]$. Measurability and boundedness of $\varphi$ are the standing assumptions that make every expectation involved finite; they are carried as explicit hypotheses.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Appendix A, Lemma A.1

import Mathlib
import Definitions.Def_SoarModel

open MeasureTheory

namespace Soar

theorem hindsight_mono {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (n : ℕ) (hn : 1 ≤ n) :
    SoarHindsight P Q φ n ≤ SoarHindsight P Q φ (n + 1) := by
  sorry

end Soar
