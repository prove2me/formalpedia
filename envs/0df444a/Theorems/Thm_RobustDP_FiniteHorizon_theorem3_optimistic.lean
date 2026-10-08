-- Prove2me | Theorems.Thm_RobustDP_FiniteHorizon_theorem3_optimistic
-- name    : RobustDP.FiniteHorizon.theorem3_optimistic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:47.76192+00:00
-- url     : https://prove2.me/theorems/0576ecce-910e-4a35-8c44-ede21a9ac40f
-- title:
--   Theorem 3 — the optimistic value function depends on the current state alone, Π_MD suffices, and recursion (18) holds
-- statement:
--   For a finite horizon AMDP with horizon $N$, let $\bar V^\pi_n(h_n)=\sup_{\mathbf P\in\mathcal T^\pi_n}E^{\mathbf P}[\sum_{t=n}^{N-1}r_t+r_N(s_N)]$ be the optimistic value of a policy and $\bar V^*_n(h_n)=\sup_\pi\bar V^\pi_n(h_n)$ the optimistic value function, the supremum taken over all history dependent randomized policies. Then there is a function $\bar V^*_n(s)$ of the epoch and the state such that:
--
--   1. for $n=0,\dots,N$ and every history $h_n$, $\bar V^*_n(h_n)=\bar V^*_n(s_n)$ depends on the current state alone;
--   2. for $n\in T=\{0,\dots,N-1\}$, the optimistic value $\bar V^\pi_n(h_n)$ of a deterministic Markov policy depends on $h_n$ only through $s_n$, and $\bar V^*_n(s_n)=\sup_{\pi\in\Pi_{MD}}\bar V^\pi_n(s_n)$;
--   3. for $n\in T$ and every state $s$,
--   $$
--   \bar V^*_n(s)=\sup_{a\in\mathcal A_n(s)}\ \sup_{p\in\mathcal P_n(s,a)}\ \sum_{s'}p(s')\big[r_n(s,a,s')+\bar V^*_{n+1}(s')\big].\tag{18}
--   $$
--
--   It is the optimistic counterpart of Theorem 2 announced in Remark 1.
--
--   **Formalization Note** The state-only function is an existentially quantified $W(n,s)$; the theorem asserts that the history-based value equals it. Clause 2 makes explicit that the page's notation $\bar V^\pi_n(s_n)$ for Markov policies is well defined.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 8, Theorem 3, eq. (18); optimistic values (6)–(7), p. 5

import Mathlib
import Definitions.Def_RobustDP_FiniteHorizon_Value

namespace RobustDP.FiniteHorizon

/-- Theorem 3 (Iyengar, TR-2002-07, p. 8), the optimistic analogue of Theorem 2. There is a
function `W(n, s)` (the state-only optimistic value `V̄*_n(s)`) such that:
1. for all `n = 0, …, N`, `V̄*_n(h_n) = W(n, s_n)`;
2. for `n ∈ T`, the optimistic value `V̄^π_n(h_n)` of a deterministic Markov policy depends on
   `h_n` only through `s_n`, and `W(n, s_n) = sup_{π ∈ Π_{MD}} V̄^π_n(s_n)`;
3. for `n ∈ T`, (18): `W(n, s) = sup_{a ∈ A(s)} sup_{p ∈ P_n(s, a)} E^p[r_n(s, a, s') + W(n + 1, s')]`. -/
theorem theorem3_optimistic {S A : Type*} [Countable S] [Countable A] (M : AMDP S A) :
    ∃ W : ℕ → S → ℝ,
      (∀ n ≤ M.N, ∀ h : History S A n, VbarStar M n h = W n h.cur) ∧
      (∀ n < M.N, ∀ π : Policy M, IsDetMarkov π →
        ∀ h h' : History S A n, h.cur = h'.cur → Vbar M π n h = Vbar M π n h') ∧
      (∀ n < M.N, ∀ h : History S A n,
        W n h.cur = ⨆ π : {π : Policy M // IsDetMarkov π}, Vbar M π.1 n h) ∧
      (∀ n < M.N, ∀ s : S,
        W n s =
          ⨆ a : M.Aset n s,
            ⨆ p : M.P n s a, expect (p : PMF S) (fun s' => M.r n s a s' + W (n + 1) s')) := by sorry

end RobustDP.FiniteHorizon
