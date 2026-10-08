-- Prove2me | Theorems.Thm_RobustDP_FiniteHorizon_corollary1_deterministic
-- name    : RobustDP.FiniteHorizon.corollary1_deterministic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:44.512279+00:00
-- url     : https://prove2.me/theorems/468e4215-a05e-47c0-b701-9290908651de
-- title:
--   Corollary 1 — history dependent deterministic policies are adequate for the robust value function
-- statement:
--   Let $\Pi_D$ be the set of history dependent deterministic policies of a finite horizon AMDP with horizon $N$. For $n=0,\dots,N-1$ and every history $h_n$,
--   $$
--   V^*_n(h_n)=\sup_{\pi\in\Pi_D}V^\pi_n(h_n),
--   $$
--   where $V^*_n(h_n)$ is the supremum of $V^\pi_n(h_n)$ over all history dependent *randomized* policies.
--
--   Randomization therefore does not improve the robust value.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 7, Corollary 1

import Mathlib
import Definitions.Def_RobustDP_FiniteHorizon_Value

namespace RobustDP.FiniteHorizon

/-- Corollary 1 (Iyengar, TR-2002-07, p. 7): the history dependent deterministic policies `Π_D`
are adequate: for `n = 0, …, N - 1`, `V*_n(h_n) = sup_{π ∈ Π_D} V^π_n(h_n)`, where `V*_n` is the
supremum over all history dependent randomized policies. -/
theorem corollary1_deterministic {S A : Type*} [Countable S] [Countable A] (M : AMDP S A) :
    ∀ n < M.N, ∀ h : History S A n,
      Vstar M n h = ⨆ π : {π : Policy M // IsDeterministic π}, V M π.1 n h := by sorry

end RobustDP.FiniteHorizon
