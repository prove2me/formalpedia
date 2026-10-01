-- Prove2me | Theorems.Thm_Soar_meta_performance
-- name    : Soar.meta_performance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-22T19:02:15.550662+00:00
-- url     : https://prove2.me/theorems/9cdd21a4-737f-48e9-9f29-b91e87ed95d0
-- title:
--   Meta performance of SOAR (Theorem 1)
-- statement:
--   **Standing conventions.** Throughout, $\mathcal X$ (demand weight vectors) and $\mathcal Y$ (supply feature vectors) are measurable spaces, $P$ and $Q$ are probability measures on them, and the match quality function $\varphi : \mathcal X \times \mathcal Y \to \mathbb R$ is jointly measurable and bounded, $|\varphi(x,y)| \le C$ for all $x, y$. Expectations over $n$ i.i.d. demand units and $n$ independent i.i.d. supply units are integrals against the product measure $P^{\otimes n} \otimes Q^{\otimes n}$ on $\mathcal X^n \times \mathcal Y^n$. The hindsight optimum value is
--   $$U^H_n = \frac{1}{n}\,\mathbb E\Bigl[\sup_{\sigma \in S_n} \sum_{t=1}^{n} \varphi\bigl(X_t, Y_{\sigma(t)}\bigr)\Bigr],$$
--   with $S_n$ the symmetric group, and the limiting hindsight optimum is $U_\infty = \sup_{n \ge 1} U^H_n$.
--
--   Let $\mathrm{opt}$ be a measurable offline assignment solver for $\varphi$: for every size $m$, every demand tuple and every supply tuple it returns a perfect assignment of maximum total quality, ties broken by any deterministic rule. Let $U_n(\mathrm{SOAR})$ be the average expected match value of the SOAR policy run with $n$ supply units drawn i.i.d. from $Q$, demand units drawn i.i.d. from $P$, simulated demand units drawn from $P$, and this solver. Then
--   $$U_n(\mathrm{SOAR}) = \frac{1}{n} \sum_{k=1}^{n} U^H_k ,$$
--   the average of the hindsight optimum values of the problems of sizes $1, \dots, n$.
--
--   **Role.** This is the paper's central result and the mission's goal. It holds for every $P$, $Q$ and bounded $\varphi$, with no structural assumption on the distributions or the quality function, and it converts every question about SOAR's performance into a question about the convergence of the hindsight optimum values: the regret of SOAR is the Cesàro average of the hindsight regrets (Remark 4), it vanishes for every bounded instance (Corollary 1), and it inherits the rate of the hindsight regret whenever that rate is regular (Corollary 2), which is how the paper obtains its near-optimal regret scalings for the $-\|x - y\|^p$ and $\langle x, y\rangle$ quality functions from the empirical optimal transport literature. The proof is the induction of properties (i) and (ii): at every epoch the remaining supply is i.i.d. $Q$ and the expected value of the current match is the hindsight optimum of the current size.
--
--   **Formalization Note** Boundedness of $\varphi$ is imposed, as in the paper, so that every expectation is finite; measurability of $\varphi$ and of the solver is the field's standing convention, made explicit. The paper allows the solver's tie-breaking to be arbitrary and the identity holds for every deterministic measurable choice; a randomized tie-breaking rule is a deterministic rule applied to an extra seed and is not modelled separately. The identity is exact, not asymptotic. With $n = 0$ both sides are the junk value $0$.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 3.2.2, Theorem 1, equation (5)

import Mathlib
import Definitions.Def_SoarPolicy

open MeasureTheory
open scoped BigOperators

namespace Soar

theorem meta_performance {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hsolver : SoarIsSolver φ opt) (hopt : SoarSolverMeasurable opt) (n : ℕ) :
    SoarValue P Q φ opt n = (∑ k ∈ Finset.Icc 1 n, SoarHindsight P Q φ k) / n := by
  sorry

end Soar
