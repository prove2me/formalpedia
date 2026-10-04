-- Prove2me | Theorems.Thm_Soar_remaining_law
-- name    : Soar.remaining_law
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-22T19:01:15.316498+00:00
-- url     : https://prove2.me/theorems/2390008d-d17f-4ed6-afc2-47c1298a0f0c
-- title:
--   The remaining supply units stay i.i.d. (property (i))
-- statement:
--   Let $\mathcal X$ and $\mathcal Y$ be measurable spaces with probability measures $P$ and $Q$, and let $\mathrm{opt}$ be a measurable offline assignment solver. Fix $k \ge 0$. Draw the remaining supply $\tilde y = (\tilde y_0, \dots, \tilde y_k)$ i.i.d. $Q$ and, independently, the epoch randomness of a SOAR epoch with $k + 1$ remaining units; let $i$ be the index of the supply unit SOAR allocates to the arriving unit. Then the relabelled remaining supply
--   $$\bigl(\tilde y_0, \dots, \tilde y_{i-1}, \tilde y_{i+1}, \dots, \tilde y_k\bigr) \in \mathcal Y^{k}$$
--   has law $Q^{\otimes k}$: the $k$ supply units carried into the next epoch are again i.i.d. $Q$.
--
--   **Role.** This is property (i) in the proof of Theorem 1, the invariant that the paper proves "inductively in $t$" and calls the key observation: SOAR never biases the pool of remaining supply, so at every epoch the supply looks like a fresh i.i.d. sample and the solver is solving a genuine hindsight problem. Property (ii), the value computation, is derived from it.
--
--   **Formalization Note** The relabelling is the order-preserving bijection skipping the matched index; the paper leaves the relabelling unspecified, and the law of the result does not depend on the choice. The statement is an identity of pushforward measures on $\mathcal Y^k$; for $k = 0$ it says the empty tuple has the trivial law.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 3.2.2, proof of Theorem 1, property (i)

import Mathlib
import Definitions.Def_SoarPolicy

open MeasureTheory

namespace Soar

theorem remaining_law {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    (hopt : SoarSolverMeasurable opt) (k : ℕ) :
    Measure.map
        (fun ω : (Fin (k + 1) → Y) × SoarEpochRand X k =>
          SoarRemaining ω.1 (SoarPick opt ω.1 ω.2))
        ((Measure.pi fun _ : Fin (k + 1) => Q).prod (SoarEpochMeasure P k))
      = Measure.pi fun _ : Fin k => Q := by
  sorry

end Soar
