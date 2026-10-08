-- Prove2me | Theorems.Thm_ReentrantScheduling_FBFS_eventual_delay_bound
-- name    : ReentrantScheduling.FBFS.eventual_delay_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:44.899757+00:00
-- url     : https://prove2.me/theorems/52caecbb-3539-42a8-a424-48ac5f000c7c
-- title:
--   Proof of Theorem 1, p. 1410 — parts released after T^(l) have delay at most Σ_{j=1}^l (Γ^(j) + τ_j)
-- statement:
--   Consider a nonacyclic flow line operated under first buffer first serve (FBFS), with releases satisfying the burstiness constraint (1) with constants $\lambda,\gamma\ge0$ and load $\rho=\lambda\bar w<1$ (3). Then there is a finite time $T$ such that every part $\pi$ released after $T$ exits the system with
--   $$e(\pi)-\alpha(\pi)\le\sum_{j=1}^{l}\big(\Gamma^{(j)}+\tau_j\big),$$
--   where $\Gamma^{(j)}$ are the busy-period constants of the proof of Theorem 1.
--
--   The bound depends only on the line and on $\lambda,\gamma$, not on the initial state; the initial state only affects the length of the transient $[0,T]$ (p. 1410).
--
--   **Formalization Note** Buffers are 0-based, and the sum runs over `Fin l`. The statement concerns released parts (initial parts are excluded). The exit time lives in `WithTop ℝ`, so the conclusion includes that the part exits.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1410, proof of Theorem 1, final paragraph

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Model
import Definitions.Def_ReentrantScheduling_FBFS_Constants

namespace ReentrantScheduling.FBFS

theorem eventual_delay_bound
    (L : Line) (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1)
    (R : Run L) (hR : R.Admissible L.fbfs) (harr : R.Arrivals lam γ) :
    ∃ T : ℝ, ∀ p : R.Part, ¬ R.initial p → T < R.α p →
      R.exit p ≤ ((R.α p + ∑ j : Fin L.l, (L.Gamma lam γ j + L.τ j) : ℝ) : WithTop ℝ) := by sorry

end ReentrantScheduling.FBFS
