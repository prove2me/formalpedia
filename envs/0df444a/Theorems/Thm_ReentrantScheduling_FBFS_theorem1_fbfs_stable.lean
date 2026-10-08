-- Prove2me | Theorems.Thm_ReentrantScheduling_FBFS_theorem1_fbfs_stable
-- name    : ReentrantScheduling.FBFS.theorem1_fbfs_stable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:51.662529+00:00
-- url     : https://prove2.me/theorems/857d444a-e7e2-4b1c-a4db-c438f3af49bb
-- title:
--   Theorem 1, p. 1409 — FBFS is stable whenever the arrivals satisfy (1) and ρ < 1
-- statement:
--   **Theorem 1 (Stability of FBFS).** Consider a nonacyclic flow line with $S$ service centers, $m_\sigma$ identical machines at center $\sigma$, route $\sigma_1,\dots,\sigma_l$ and processing times $\tau_1,\dots,\tau_l>0$. Let $\lambda,\gamma\ge0$ with load
--   $$\rho=\max_\sigma\lambda w_\sigma<1,\qquad w_\sigma=\sum_{i:\,\sigma_i=\sigma}\frac{\tau_i}{m_\sigma}.$$
--   Then every admissible run of the first buffer first serve (FBFS) policy whose releases satisfy the burstiness constraint
--   $$u(t)-u(s)\le\lambda(t-s)+\gamma\qquad(0\le s\le t)$$
--   is stable: there is $\Gamma\ge0$ such that every part $\pi$, initial or released, exits the system and
--   $$e(\pi)-\alpha(\pi)\le\Gamma .$$
--
--   The constant $\Gamma$ may depend on the run, in particular on the initial state (p. 1409). Theorem 1 shows that the "push" policy which always serves the earliest buffer at a center never lets delays grow without bound when the arrival rate is within capacity, in contrast with Example 1, where another buffer priority policy is unstable.
--
--   **Formalization Note** The run model is the one of the Model definition: nonidling, nonpreemptive, head-of-buffer dispatch with FBFS priority (`L.fbfs`), times in `WithTop ℝ` so that a never-served part has exit time $\top$, and counts by `Set.encard`. Initial parts have $\alpha(\pi)=0$. The pinned hypothesis $\tau_i>0$ is part of the line data. $\Gamma$ is quantified after the run, as on the page.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1409, Theorem 1; proof pp. 1409–1410

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Model

namespace ReentrantScheduling.FBFS

theorem theorem1_fbfs_stable
    (L : Line) (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1)
    (R : Run L) (hR : R.Admissible L.fbfs) (harr : R.Arrivals lam γ) :
    R.Stable := by sorry

end ReentrantScheduling.FBFS
