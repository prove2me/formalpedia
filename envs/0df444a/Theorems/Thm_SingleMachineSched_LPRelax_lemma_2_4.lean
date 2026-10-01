-- Prove2me | Theorems.Thm_SingleMachineSched_LPRelax_lemma_2_4
-- name    : SingleMachineSched.LPRelax.lemma_2_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T04:12:23.805998+00:00
-- url     : https://prove2.me/theorems/4a3a87b0-9eb6-4e57-a0d1-9496e0824003
-- title:
--   Lemma 2.4 — the shifted parallel inequalities (2.3) and their equality case
-- statement:
--   Let $n$ jobs have integral processing times $p_j > 0$ and integral release dates $r_j \ge 0$. Let $(A_j)_j$ be any preemptive schedule, with mean busy times $M_j = \frac{1}{p_j}\int_{A_j} t\,dt$, and let $S$ be a nonempty set of jobs, with $p(S) = \sum_{j\in S} p_j$ and $r_{\min}(S) = \min_{j \in S} r_j$. Then
--
--   $$\sum_{j \in S} p_j M_j \ge p(S)\Big(r_{\min}(S) + \frac12 p(S)\Big), \tag{2.3}$$
--
--   and equality holds if and only if the jobs of $S$ occupy the machine without interruption from $r_{\min}(S)$ to $r_{\min}(S) + p(S)$, that is, $\bigcup_{j \in S} A_j$ coincides with $[r_{\min}(S), r_{\min}(S) + p(S))$ up to a set of measure zero.
--
--   The inequality shows that the mean busy time vector of every preemptive schedule is feasible for (R), so $Z_R$ is a lower bound; the equality case is what makes the LP schedule's mean busy times attain it.
--
--   **Formalization Note** Processing sets are determined only up to null sets as far as $M_j$ is concerned, so "scheduled without interruption" is rendered as almost-everywhere equality of sets for Lebesgue measure. The paper's statement ranges over all sets $S$; for $S = \emptyset$ it is $0 \ge 0$ and $r_{\min}(\emptyset)$ is undefined, so $S$ is nonempty here.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 172, Lemma 2.4 and inequality (2.3)

import Mathlib
import Definitions.Def_SingleMachineSched_Shared_PreemptiveSchedule
import Definitions.Def_SingleMachineSched_Shared_RelaxationR

namespace SingleMachineSched.LPRelax

/-- Lemma 2.4: in every preemptive schedule, every nonempty job set `S` satisfies the shifted
parallel inequality (2.3), with equality iff the jobs of `S` occupy the machine without
interruption from `r_min(S)` to `r_min(S) + p(S)` (up to a null set of times). -/
theorem lemma_2_4 {n : ℕ} (p r : Fin n → ℕ) (hp : ∀ j, 0 < p j) (A : Fin n → Set ℝ)
    (hA : Shared.IsPreemptiveSchedule p r A) (S : Finset (Fin n)) (hS : S.Nonempty) :
    Shared.pSum p S * (Shared.rmin r S hS + Shared.pSum p S / 2) ≤ ∑ j ∈ S, (p j : ℝ) * Shared.meanBusyTime p A j ∧
      (∑ j ∈ S, (p j : ℝ) * Shared.meanBusyTime p A j = Shared.pSum p S * (Shared.rmin r S hS + Shared.pSum p S / 2) ↔
        (⋃ j ∈ S, A j) =ᵐ[MeasureTheory.volume]
          Set.Ico (Shared.rmin r S hS) (Shared.rmin r S hS + Shared.pSum p S)) := by sorry

end SingleMachineSched.LPRelax
