-- Prove2me | Theorems.Thm_ReentrantScheduling_FBFS_gamma1_busy_period_bound
-- name    : ReentrantScheduling.FBFS.gamma1_busy_period_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:50.884981+00:00
-- url     : https://prove2.me/theorems/a2913ceb-3a85-49e9-9938-f36ca47b6c9d
-- title:
--   Proof of Theorem 1, p. 1409 — a 1-busy period commencing at T₁ > 0 lasts at most Γ^(1)
-- statement:
--   Consider a nonacyclic flow line operated under first buffer first serve (FBFS), with releases satisfying the burstiness constraint (1) with constants $\lambda,\gamma\ge0$ and load $\rho=\lambda\bar w<1$ (3). Let $0<T_1\le T_2$, and suppose that:
--   1. a 1-busy period commences at $T_1$: for some $\delta>0$, no part waits in buffer $b_1$ at any time in $(T_1-\delta,T_1)$;
--   2. $[T_1,T_2]$ is a 1-busy period: at every $t\in[T_1,T_2]$ some part waits in $b_1$.
--
--   Then
--   $$T_2-T_1\le\Gamma^{(1)}=\Big(2\bar\tau+\frac{\gamma\tau_1}{m_{\sigma_1}}\Big)\Big(1-\frac{\lambda\tau_1}{m_{\sigma_1}}\Big)^{-1},\qquad \bar\tau=\max_j\tau_j .$$
--
--   This is the base case of the induction that proves Theorem 1: once buffer $b_1$ has emptied, it never stays continuously occupied for longer than $\Gamma^{(1)}$.
--
--   **Formalization Note** Buffer $b_1$ is Lean index `0`. The page assumes $T_1>T^{(1)}$, the first time $b_1$ empties, only to make "commences" meaningful; the statement assumes the commencing condition itself and $T_1>0$, a mild generalization. Waiting excludes parts in service, as $x_i(t)$ does on p. 1409.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1409, proof of Theorem 1, the case i = 1 (bound on Γ^(1))

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Model
import Definitions.Def_ReentrantScheduling_FBFS_Constants

namespace ReentrantScheduling.FBFS

theorem gamma1_busy_period_bound
    (L : Line) (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1)
    (R : Run L) (hR : R.Admissible L.fbfs) (harr : R.Arrivals lam γ)
    (T₁ T₂ : ℝ) (hT₁ : 0 < T₁) (hT₁₂ : T₁ ≤ T₂)
    (hcommence : ∃ δ > 0, ∀ t : ℝ, T₁ - δ < t → t < T₁ →
      ∀ q, ¬ R.Waiting q ⟨0, L.l_pos⟩ t)
    (hbusy : ∀ t : ℝ, T₁ ≤ t → t ≤ T₂ → R.Busy ⟨0, L.l_pos⟩ t) :
    T₂ - T₁ ≤ L.Gamma lam γ ⟨0, L.l_pos⟩ := by sorry

end ReentrantScheduling.FBFS
