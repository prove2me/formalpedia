-- Prove2me | Theorems.Thm_Soar_pick_law
-- name    : Soar.pick_law
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-22T19:00:18.589954+00:00
-- url     : https://prove2.me/theorems/aa279a95-7b0c-4359-b420-9ef7af5c827f
-- title:
--   Every remaining supply unit is equally likely to be matched
-- statement:
--   Let $\mathcal X$ and $\mathcal Y$ be measurable spaces with probability measures $P$ and $Q$, and let $\mathrm{opt}$ be a measurable offline assignment solver (for every size $m$, a measurable map from demand tuples and supply tuples in $\mathcal X^m \times \mathcal Y^m$ to permutations in $S_m$; no optimality is needed here). Fix $k \ge 0$. Draw the remaining supply $\tilde y = (\tilde y_0, \dots, \tilde y_k)$ i.i.d. $Q$ and, independently, the epoch randomness $(\hat x_0, (\hat x_1, \dots, \hat x_k), \sigma)$ of a SOAR epoch with $k + 1$ remaining units; let $i = \eta^\star(\sigma^{-1}(0))$ with $\eta^\star = \mathrm{opt}\bigl((\hat x_{\sigma(j)})_j, \tilde y\bigr)$ be the index of the supply unit SOAR allocates to the arriving unit. Then the joint law of
--   $$\bigl(\tilde y,\ i\bigr)$$
--   is $Q^{\otimes (k+1)} \otimes \mathrm{Unif}\{0, \dots, k\}$: the matched index is uniform over the remaining units and independent of their feature vectors.
--
--   **Role.** This is the property $\mathbb P(A_i) = \frac{1}{n-t+1}$ of the proof of Theorem 1, where $A_i$ is the event that $\tilde Y_i$ is matched to $X_t$: the paper derives it from the conditional computation of the previous milestone and notes that it holds for any tie-breaking rule of the solver. It is the exchangeability that keeps the remaining supply i.i.d. and makes the per-epoch value equal to a hindsight optimum.
--
--   **Formalization Note** The solver may be an arbitrary measurable rule here; optimality is only needed for the value computation. The statement is an identity of pushforward measures on $\mathcal Y^{k+1} \times \{0, \dots, k\}$.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 3.2.2, proof of Theorem 1 (the conclusion $\mathbb P(A_i) = \frac{1}{n-t+1}$)

import Mathlib
import Definitions.Def_SoarPolicy

open MeasureTheory

namespace Soar

theorem pick_law {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hopt : SoarSolverMeasurable opt) (k : ℕ) :
    Measure.map (fun ω : (Fin (k + 1) → Y) × SoarEpochRand X k => (ω.1, SoarPick opt ω.1 ω.2))
        ((Measure.pi fun _ : Fin (k + 1) => Q).prod (SoarEpochMeasure P k))
      = (Measure.pi fun _ : Fin (k + 1) => Q).prod (SoarUniform (Fin (k + 1))) := by
  sorry

end Soar
