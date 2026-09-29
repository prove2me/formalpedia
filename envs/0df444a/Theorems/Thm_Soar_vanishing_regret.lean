-- Prove2me | Theorems.Thm_Soar_vanishing_regret
-- name    : Soar.vanishing_regret
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-22T19:03:11.517208+00:00
-- url     : https://prove2.me/theorems/94b9ddfc-57e6-46d2-8514-15ae87060ef6
-- title:
--   SOAR achieves vanishing regret (Corollary 1)
-- statement:
--   **Standing conventions.** Throughout, $\mathcal X$ (demand weight vectors) and $\mathcal Y$ (supply feature vectors) are measurable spaces, $P$ and $Q$ are probability measures on them, and the match quality function $\varphi : \mathcal X \times \mathcal Y \to \mathbb R$ is jointly measurable and bounded, $|\varphi(x,y)| \le C$ for all $x, y$. Expectations over $n$ i.i.d. demand units and $n$ independent i.i.d. supply units are integrals against the product measure $P^{\otimes n} \otimes Q^{\otimes n}$ on $\mathcal X^n \times \mathcal Y^n$. The hindsight optimum value is
--   $$U^H_n = \frac{1}{n}\,\mathbb E\Bigl[\sup_{\sigma \in S_n} \sum_{t=1}^{n} \varphi\bigl(X_t, Y_{\sigma(t)}\bigr)\Bigr],$$
--   with $S_n$ the symmetric group, and the limiting hindsight optimum is $U_\infty = \sup_{n \ge 1} U^H_n$.
--
--   Let $\mathrm{opt}$ be a measurable offline assignment solver for $\varphi$ and let $\mathrm{Reg}_n(\mathrm{SOAR}) = U_\infty - U_n(\mathrm{SOAR})$ be the regret of SOAR with $n$ supply units. Then SOAR achieves vanishing regret:
--   $$\lim_{n \to \infty} \mathrm{Reg}_n(\mathrm{SOAR}) = 0 .$$
--
--   **Role.** This is Corollary 1. Its proof (Appendix C) combines the regret decomposition of Remark 4 with the facts, from Appendix A, that the hindsight regrets $\mathrm{Reg}_k(\mathrm{H\text{-}OPT})$ form a nonnegative decreasing sequence with limit $0$; the Cesàro average of such a sequence tends to $0$. No assumption on $P$, $Q$ or $\varphi$ beyond boundedness is used.
--
--   **Formalization Note** Only the standing hypotheses of Theorem 1 appear. The limit is along $n \to \infty$ in the natural numbers; the junk value at $n = 0$ is irrelevant.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 3.2.2, Corollary 1, and Appendix C

import Mathlib
import Definitions.Def_SoarPolicy

open MeasureTheory Filter Topology

namespace Soar

theorem vanishing_regret {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hsolver : SoarIsSolver φ opt) (hopt : SoarSolverMeasurable opt) :
    Tendsto (fun n : ℕ => SoarRegret P Q φ opt n) atTop (𝓝 0) := by
  sorry

end Soar
