-- Prove2me | Theorems.Thm_Soar_regret_decomposition
-- name    : Soar.regret_decomposition
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-22T19:02:48.992416+00:00
-- url     : https://prove2.me/theorems/5decee1e-9232-4a5f-8d86-e712305f40be
-- title:
--   Regret decomposition of SOAR (Remark 4)
-- statement:
--   **Standing conventions.** Throughout, $\mathcal X$ (demand weight vectors) and $\mathcal Y$ (supply feature vectors) are measurable spaces, $P$ and $Q$ are probability measures on them, and the match quality function $\varphi : \mathcal X \times \mathcal Y \to \mathbb R$ is jointly measurable and bounded, $|\varphi(x,y)| \le C$ for all $x, y$. Expectations over $n$ i.i.d. demand units and $n$ independent i.i.d. supply units are integrals against the product measure $P^{\otimes n} \otimes Q^{\otimes n}$ on $\mathcal X^n \times \mathcal Y^n$. The hindsight optimum value is
--   $$U^H_n = \frac{1}{n}\,\mathbb E\Bigl[\sup_{\sigma \in S_n} \sum_{t=1}^{n} \varphi\bigl(X_t, Y_{\sigma(t)}\bigr)\Bigr],$$
--   with $S_n$ the symmetric group, and the limiting hindsight optimum is $U_\infty = \sup_{n \ge 1} U^H_n$.
--
--   Let $\mathrm{opt}$ be a measurable offline assignment solver for $\varphi$ and let $U_n(\mathrm{SOAR})$ be the average expected match value of SOAR with $n$ supply units. Then for every $n \ge 1$ the regret of SOAR is the average of the regrets of the hindsight-optimal algorithm on the horizons $1, \dots, n$:
--   $$\mathrm{Reg}_n(\mathrm{SOAR}) = U_\infty - U_n(\mathrm{SOAR}) = \frac{1}{n} \sum_{k=1}^{n} \bigl(U_\infty - U^H_k\bigr) = \frac{1}{n} \sum_{k=1}^{n} \mathrm{Reg}_k(\mathrm{H\text{-}OPT}) .$$
--
--   **Role.** This is Remark 4, the form of Theorem 1 that the corollaries use: the regret of SOAR is the Cesàro sum of the hindsight regrets, so it converges to $0$ whenever they do and it converges at their rate whenever that rate is regular.
--
--   **Formalization Note** The identity is Theorem 1 with $U_\infty$ subtracted from both sides and $U_\infty = \frac1n \sum_{k=1}^n U_\infty$; the restriction $n \ge 1$ is needed because for $n = 0$ the left side is $U_\infty$ while the right side is the junk value $0$.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 3.2.2, Remark 4

import Mathlib
import Definitions.Def_SoarPolicy

open MeasureTheory
open scoped BigOperators

namespace Soar

theorem regret_decomposition {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hsolver : SoarIsSolver φ opt) (hopt : SoarSolverMeasurable opt) (n : ℕ) (hn : 1 ≤ n) :
    SoarRegret P Q φ opt n = (∑ k ∈ Finset.Icc 1 n, SoarRegretH P Q φ k) / n := by
  sorry

end Soar
