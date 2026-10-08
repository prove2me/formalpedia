-- Prove2me | Theorems.Thm_ReentrantScheduling_FBFS_busy_period_bound
-- name    : ReentrantScheduling.FBFS.busy_period_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:48.33998+00:00
-- url     : https://prove2.me/theorems/d4fe575c-72bf-4d09-b267-30ce0a0e3d79
-- title:
--   Proof of Theorem 1, pp. 1409–1410 — after finite times T^(i), every i-busy period lasts at most Γ^(i)
-- statement:
--   Consider a nonacyclic flow line operated under first buffer first serve (FBFS), with releases satisfying the burstiness constraint (1) with constants $\lambda,\gamma\ge0$ and load $\rho=\lambda\bar w<1$ (3). Then there are finite times $T^{(1)},\dots,T^{(l)}$ such that for every buffer index $i$ and every $i$-busy period $[T_1,T_2]$ with $T_1>T^{(i)}$,
--   $$T_2-T_1\le\Gamma^{(i)},$$
--   where $\Gamma^{(i)}$ is defined recursively by $\bar\Gamma=\sum_{j=1}^{i-1}(\Gamma^{(j)}+\tau_j)$ and
--   $$\Gamma^{(i)}=\Big[2\bar\tau+\sum_{j:\ \sigma_j=\sigma_i,\ j\le i}\frac{\lambda\tau_j\bar\Gamma+\gamma\tau_j}{m_{\sigma_i}}\Big]\Big[1-\sum_{j:\ \sigma_j=\sigma_i,\ j\le i}\frac{\lambda\tau_j}{m_{\sigma_i}}\Big]^{-1}.$$
--   An $i$-busy period is an interval at every instant of which some part waits in a buffer $b_j$, $j\le i$, at the center $\sigma_i$.
--
--   This is the induction hypothesis of the proof of Theorem 1, established for every $i$; the constants depend only on the line and on $\lambda,\gamma$, while the times $T^{(i)}$ depend on the run, in particular on the initial state.
--
--   **Formalization Note** Buffers are 0-based (`i` is the paper's $i+1$). The page prints $\Gamma^{(i)}$ as a product of the two brackets; the Lean uses the quotient that the preceding inequality yields (see the Constants definition). The times $T^{(i)}$ are existentially quantified after the run.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1409, proof of Theorem 1, the induction hypothesis; p. 1410, Γ^(i)

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Model
import Definitions.Def_ReentrantScheduling_FBFS_Constants

namespace ReentrantScheduling.FBFS

theorem busy_period_bound
    (L : Line) (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1)
    (R : Run L) (hR : R.Admissible L.fbfs) (harr : R.Arrivals lam γ) :
    ∃ T : Fin L.l → ℝ, ∀ (i : Fin L.l) (T₁ T₂ : ℝ), T i < T₁ → T₁ ≤ T₂ →
      (∀ t : ℝ, T₁ ≤ t → t ≤ T₂ → R.Busy i t) →
      T₂ - T₁ ≤ L.Gamma lam γ i := by sorry

end ReentrantScheduling.FBFS
