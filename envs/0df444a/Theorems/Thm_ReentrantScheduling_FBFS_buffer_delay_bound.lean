-- Prove2me | Theorems.Thm_ReentrantScheduling_FBFS_buffer_delay_bound
-- name    : ReentrantScheduling.FBFS.buffer_delay_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:06.702979+00:00
-- url     : https://prove2.me/theorems/261d09e6-ca15-4584-a62d-16d66033a5a4
-- title:
--   Proof of Theorem 1, p. 1409 — a part reaching b_j after T^(j) leaves b_j within Γ^(j) + τ_j
-- statement:
--   Consider a nonacyclic flow line operated under first buffer first serve (FBFS), with releases satisfying the burstiness constraint (1) with constants $\lambda,\gamma\ge0$ and load $\rho=\lambda\bar w<1$ (3). Then there are finite times $T^{(1)},\dots,T^{(l)}$ such that every part $\pi$ that arrives at buffer $b_j$ at a time $\alpha_j(\pi)>T^{(j)}$ is served there and completes its service at $b_j$ by
--   $$\alpha_j(\pi)+\Gamma^{(j)}+\tau_j ,$$
--   with $\Gamma^{(j)}$ the busy-period constant of the proof of Theorem 1. In words: the delay of a part at $b_j$ is at most $\Gamma^{(j)}+\tau_j$ if it arrived at $b_j$ after $T^{(j)}$.
--
--   Summing these delays along the route gives the bound $\bar\Gamma=\sum_{j<i}(\Gamma^{(j)}+\tau_j)$ on the time a part needs to reach $b_i$, which feeds the induction step.
--
--   **Formalization Note** Buffers are 0-based. The delay at $b_j$ is measured from arrival at $b_j$ to the end of service there. Arrival and start times live in `WithTop ℝ`; the conclusion forces the service start to be finite.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1409, proof of Theorem 1, last paragraph of the right column

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Model
import Definitions.Def_ReentrantScheduling_FBFS_Constants

namespace ReentrantScheduling.FBFS

theorem buffer_delay_bound
    (L : Line) (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1)
    (R : Run L) (hR : R.Admissible L.fbfs) (harr : R.Arrivals lam γ) :
    ∃ T : Fin L.l → ℝ, ∀ (j : Fin L.l) (p : R.Part), R.entry p ≤ j →
      ((T j : ℝ) : WithTop ℝ) < R.arrive p j →
      R.start p j + ((L.τ j : ℝ) : WithTop ℝ) ≤
        R.arrive p j + ((L.Gamma lam γ j + L.τ j : ℝ) : WithTop ℝ) := by sorry

end ReentrantScheduling.FBFS
