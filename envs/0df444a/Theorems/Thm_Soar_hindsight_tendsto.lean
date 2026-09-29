-- Prove2me | Theorems.Thm_Soar_hindsight_tendsto
-- name    : Soar.hindsight_tendsto
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-22T18:59:12.46854+00:00
-- url     : https://prove2.me/theorems/7142cecd-d2b5-49e4-b385-02e96dce1c43
-- title:
--   Existence of the limiting hindsight optimum
-- statement:
--   **Standing conventions.** Throughout, $\mathcal X$ (demand weight vectors) and $\mathcal Y$ (supply feature vectors) are measurable spaces, $P$ and $Q$ are probability measures on them, and the match quality function $\varphi : \mathcal X \times \mathcal Y \to \mathbb R$ is jointly measurable and bounded, $|\varphi(x,y)| \le C$ for all $x, y$. Expectations over $n$ i.i.d. demand units and $n$ independent i.i.d. supply units are integrals against the product measure $P^{\otimes n} \otimes Q^{\otimes n}$ on $\mathcal X^n \times \mathcal Y^n$. The hindsight optimum value is
--   $$U^H_n = \frac{1}{n}\,\mathbb E\Bigl[\sup_{\sigma \in S_n} \sum_{t=1}^{n} \varphi\bigl(X_t, Y_{\sigma(t)}\bigr)\Bigr],$$
--   with $S_n$ the symmetric group, and the limiting hindsight optimum is $U_\infty = \sup_{n \ge 1} U^H_n$.
--
--   Then the sequence of hindsight optimum values converges to the limiting hindsight optimum, and is dominated by it:
--   $$\lim_{n \to \infty} U^H_n = U_\infty, \qquad\text{and}\qquad U^H_n \le U_\infty \quad \text{for every } n \ge 1 .$$
--   Equivalently, the hindsight regrets $\mathrm{Reg}_n(\mathrm{H\text{-}OPT}) = U_\infty - U^H_n$ are nonnegative for $n \ge 1$ and tend to $0$.
--
--   **Role.** This is the statement of Section 2 that the limiting hindsight optimum exists, "guaranteed by the boundedness and monotonicity of $U^H_n$", together with the first inequality of the chain $U_\infty \ge U^H_n \ge U_n(\pi)$ that Appendix A is devoted to. It is the input to Corollary 1 (vanishing regret of SOAR) and to the scaling corollaries.
--
--   **Formalization Note** Since $U_\infty$ is defined as $\sup_{n \ge 1} U^H_n$, the content is that the supremum is the limit, which follows from Lemma A.1 and boundedness. The restriction $n \ge 1$ in the second clause excludes the junk value $U^H_0 = 0$.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 2 and Appendix A (existence of $U_\infty$ and $U_\infty \ge U^H_n$)

import Mathlib
import Definitions.Def_SoarModel

open MeasureTheory Filter Topology

namespace Soar

theorem hindsight_tendsto {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C) :
    Tendsto (fun n : ℕ => SoarHindsight P Q φ n) atTop (𝓝 (SoarLimit P Q φ)) ∧
      ∀ n : ℕ, 1 ≤ n → SoarHindsight P Q φ n ≤ SoarLimit P Q φ := by
  sorry

end Soar
