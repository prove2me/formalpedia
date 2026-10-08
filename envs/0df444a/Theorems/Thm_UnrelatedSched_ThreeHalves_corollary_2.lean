-- Prove2me | Theorems.Thm_UnrelatedSched_ThreeHalves_corollary_2
-- name    : UnrelatedSched.ThreeHalves.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:36:33.321332+00:00
-- url     : https://prove2.me/theorems/0827226d-1ee7-4cc2-a8ac-5ffcc15d8e38
-- title:
--   Corollary 2 — for ρ < 3/2, a ρ-approximate schedule of the reduced instance decides 3-dimensional matching
-- statement:
--   The paper states: for every $\rho < 3/2$, there does not exist a polynomial $\rho$-approximation algorithm for the minimum makespan problem on unrelated parallel machines, unless $P = NP$. Its proof (an immediate consequence of Theorem 5) establishes the following, which is what is formalized.
--
--   Let $T_1,\dots,T_m$ be an instance of 3-dimensional matching and consider the scheduling instance of Theorem 5 built from it. Let $\rho < 3/2$ and let $\sigma$ be a schedule of this instance that is within the factor $\rho$ of every schedule $\tau$ of the same instance, $C_{\max}(\sigma) \le \rho\, C_{\max}(\tau)$. Then
--   $$C_{\max}(\sigma) \le 2 \quad\Longleftrightarrow\quad \text{the instance has a 3-dimensional matching.}$$
--
--   So the schedule returned by any $\rho$-approximation algorithm with $\rho < 3/2$, run on the reduced instance, answers 3-DIMENSIONAL MATCHING; a polynomial such algorithm would therefore decide an NP-complete problem in polynomial time.
--
--   **Formalization Note** "Polynomial", "NP" and "unless $P = NP$" are not formalized. The $\rho$-approximation property is the hypothesis $C_{\max}(\sigma) \le \rho\,C_{\max}(\tau)$ for all schedules $\tau$ of the same reduced instance. The bound $\rho < 3/2$ is strict, as in the paper. Values $\rho < 1$ are allowed, as in the paper's "for every $\rho < 3/2$"; for them the hypothesis can only hold in degenerate instances.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 8, Corollary 2

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_ThreeHalves_ThreeDimMatching
import Definitions.Def_UnrelatedSched_ThreeHalves_Theorem5Instance

open MatousekLP.Scheduling

namespace UnrelatedSched.ThreeHalves

/-- Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), §4, Corollary 2, p. 8 (the content of its
proof): let `ρ < 3/2` and let `σ` be a schedule of the instance of Theorem 5 built from the
3-dimensional matching instance `T` that is within the factor `ρ` of every schedule of that
instance. Then `σ` has makespan at most `2` if and only if `T` has a matching; so the output of
any `ρ`-approximation algorithm on this instance decides 3-DIMENSIONAL MATCHING. -/
theorem corollary_2 {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (ρ : ℝ) (hρ : ρ < 3 / 2)
    (σ : Fin (numJobs T) → Fin m)
    (hσ : ∀ τ : Fin (numJobs T) → Fin m,
      makespan (fun i r => (P T i r : ℝ)) σ ≤ ρ * makespan (fun i r => (P T i r : ℝ)) τ) :
    makespan (fun i r => (P T i r : ℝ)) σ ≤ 2 ↔ HasMatching T := by sorry

end UnrelatedSched.ThreeHalves
