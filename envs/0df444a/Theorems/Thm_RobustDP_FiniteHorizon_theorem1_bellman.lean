-- Prove2me | Theorems.Thm_RobustDP_FiniteHorizon_theorem1_bellman
-- name    : RobustDP.FiniteHorizon.theorem1_bellman
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:21.462608+00:00
-- url     : https://prove2.me/theorems/52a0de31-f82a-4d2c-8d6e-7944cdfc5745
-- title:
--   Theorem 1 (Bellman equation) — the robust value function on histories satisfies the robust Bellman equation (11)
-- statement:
--   Let $V^*_n(h_n)=\sup_{\pi}V^\pi_n(h_n)$ be the robust value function of a finite horizon AMDP with horizon $N$, the supremum taken over all history dependent randomized policies. Then $V^*_N(h_N)=r_N(s_N)$ for every history $h_N$, and for $n=0,\dots,N-1$ and every history $h_n$ with current state $s_n$,
--   $$
--   V^*_n(h_n)=\sup_{a\in\mathcal A_n(s_n)}\ \inf_{p\in\mathcal P_n(s_n,a)}\ \sum_{s\in\mathcal S}p(s)\Big[r_n(s_n,a,s)+V^*_{n+1}(h_n,a,s)\Big].\tag{11}
--   $$
--
--   This is the robust counterpart of the Bellman recursion; it is where the Rectangularity assumption enters. The ambiguity sets $\mathcal P_n(s_n,a)$ are arbitrary nonempty sets of measures (not necessarily convex), and the state and action sets may be countably infinite.
--
--   **Formalization Note** The page writes $\mathcal P(s_n,a)$ in (11); it is the epoch-$n$ set $\mathcal P_n(s_n,a)$, as in (15)–(16). Rewards are bounded (see the model definition).
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 6, Theorem 1 (Bellman equation), eq. (11)

import Mathlib
import Definitions.Def_RobustDP_FiniteHorizon_Value

namespace RobustDP.FiniteHorizon

/-- Theorem 1 (Bellman equation) (Iyengar, TR-2002-07, p. 6): the robust value functions
`V*_n`, `n = 0, …, N`, on histories satisfy `V*_N(h_N) = r_N(s_N)` and, for `n = 0, …, N - 1`,
`V*_n(h_n) = sup_{a ∈ A(s_n)} inf_{p ∈ P_n(s_n, a)} E^p[r_n(s_n, a, s) + V*_{n+1}(h_n, a, s)]` (11). -/
theorem theorem1_bellman {S A : Type*} [Countable S] [Countable A] (M : AMDP S A) :
    (∀ h : History S A M.N, Vstar M M.N h = M.rN h.cur) ∧
    ∀ n < M.N, ∀ h : History S A n,
      Vstar M n h =
        ⨆ a : M.Aset n h.cur,
          ⨅ p : M.P n h.cur a,
            expect (p : PMF S) (fun s => M.r n h.cur a s + Vstar M (n + 1) (h.extend a s)) := by sorry

end RobustDP.FiniteHorizon
