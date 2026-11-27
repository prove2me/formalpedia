-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaJSched_Supplement_theorem_2_7
-- name    : SingleMachineSched.AlphaJSched.Supplement.theorem_2_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T01:09:34.500613+00:00
-- url     : https://prove2.me/theorems/522be35c-b709-4762-93a5-88dc45ccd4d7
-- title:
--   Theorem 2.7 (corrected: finite real moments) — three polyhedral characterizations
-- statement:
--   Let jobs have integral processing times $p_j>0$ and release dates $r_j\ge0$. Let $P_R$ be the feasible region of (R), and let $\mathcal B$ be the mean busy time vectors of all feasible preemptive schedules. Let $P_D^\infty$ be the infinite-horizon time-indexed feasible region. Then
--   $$P_R=\operatorname{conv}(\mathcal B),$$
--   every extreme point of $P_R$ is the mean busy time vector of the LP schedule for some priority order, and
--   $$P_R=\mathcal M\!\left(\{y\in P_D^\infty:\text{every first-moment series converges}\}\right).$$
--   Here $\mathcal M(y)_j=p_j^{-1}\sum_{\tau\ge r_j}y_{j\tau}(\tau+\tfrac12)$. All three assertions are retained in one theorem. They relate feasible mean busy times to actual preemptive schedules and to fractional slot allocations.
--
--   **Formalization Note** The convex hull has no closure. Preemptive schedules reuse the published measurable, disjoint and bounded processing sets; no fixed horizon is imposed on their collection. The first-moment qualification repairs the displayed real map, without imposing finite support. The correction excludes divergent-tail allocations from the map's domain, not any scheduling instance or real mean vector.
--
--   Differences from the source:
--   - encoding: jobs 1 through n, integral p_j > 0 and r_j >= 0 → Fin n jobs with natural-valued p and r and an explicit hp hypothesis; reason: zero-based labels change no instance; the empty instance has zero cost and makespan
--   - encoding: convex hull, vertices, and an LP schedule → convexHull without closure, Set.extremePoints, and an existential priority permutation applied to the published mLP; reason: the theorem is weight-free and a vertex may require any priority order, rather than the fixed order of a given weight vector
--   - correction: the displayed map sends every y in P_D^infinity to a real vector → the image is taken over feasible y with every first-moment series Summable; reason: on p. 174 the real codomain is incompatible with divergent moments: one job p=1, r=0 and y_tau=1/((tau+1)(tau+2)) is feasible but has infinite first moment; the displayed real formula requires this convergence domain (DISPROOF.md)
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), DOI 10.1137/S089548019936223X, p. 174 (PDF 10), Theorem 2.7

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_Supplement_InfiniteD
import Definitions.Def_SingleMachineSched_Shared_PreemptiveSchedule
import Definitions.Def_SingleMachineSched_Shared_RelaxationR
import Definitions.Def_SingleMachineSched_AlphaJSched_LPSchedule

namespace SingleMachineSched.AlphaJSched.Supplement

/-- Theorem 2.7, all three polyhedral conclusions. In (ii) the displayed map
into ℝ^N is restricted to finite first moments; see DISPROOF.md for the divergent-tail case. -/
theorem theorem_2_7 {n : ℕ} (p r : Fin n → ℕ) (hp : ∀ j, 0 < p j) :
    ({M : Fin n → ℝ | Shared.FeasibleR p r M} =
      convexHull ℝ {M | ∃ A : Fin n → Set ℝ,
        Shared.IsPreemptiveSchedule p r A ∧
          M = fun j => Shared.meanBusyTime p A j}) ∧
    (∀ M ∈ Set.extremePoints ℝ {M : Fin n → ℝ | Shared.FeasibleR p r M},
      ∃ σ : Equiv.Perm (Fin n),
        M = fun j => mLP (p ∘ σ) (r ∘ σ) (σ.symm j)) ∧
    ({M : Fin n → ℝ | Shared.FeasibleR p r M} =
      mMap p '' {y | FeasibleDinf p r y ∧
        ∀ j, Summable (fun τ : ℕ => y j τ * ((τ : ℝ) + 1 / 2))}) := by sorry

end SingleMachineSched.AlphaJSched.Supplement
