-- Prove2me | Theorems.Thm_RobustDP_FiniteHorizon_theorem2_markov_optimality
-- name    : RobustDP.FiniteHorizon.theorem2_markov_optimality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:37.246087+00:00
-- url     : https://prove2.me/theorems/f3a4b69a-2327-41a8-8f75-c917b7e8570b
-- title:
--   Theorem 2 (Markov optimality) — V*ₙ depends on the current state alone, Π_MD suffices, and the robust Bellman equation reduces to (16)
-- statement:
--   Let $V^*_n(h_n)=\sup_\pi V^\pi_n(h_n)$ be the robust value function of a finite horizon AMDP with horizon $N$, the supremum taken over all history dependent randomized policies, against the rectangular, history dependent adversary. Then there is a function $V^*_n(s)$ of the epoch and the state such that:
--
--   1. for all $n=0,\dots,N$ and every history $h_n$, $V^*_n(h_n)=V^*_n(s_n)$: the robust value function is a function of the current state alone;
--   2. for $n\in T=\{0,\dots,N-1\}$, the robust value $V^\pi_n(h_n)$ of a deterministic Markov policy depends on $h_n$ only through $s_n$, and
--   $$
--   V^*_n(s_n)=\sup_{\pi\in\Pi_{MD}}V^\pi_n(s_n),
--   $$
--   where $\Pi_{MD}$ is the set of deterministic Markov policies;
--   3. for $n\in T$ and every state $s$, the robust Bellman equation (11) reduces to
--   $$
--   V^*_n(s)=\sup_{a\in\mathcal A_n(s)}\ \inf_{p\in\mathcal P_n(s,a)}\ \sum_{s'}p(s')\big[r_n(s,a,s')+V^*_{n+1}(s')\big].\tag{16}
--   $$
--
--   The recursion (16) is the basis of robust dynamic programming: once $V^*_{n+1}$ is known, computing $V^*_n$ reduces to the one-stage problems $\inf_{p\in\mathcal P_n(s,a)}E^p[v]$, and deterministic Markov policies lose nothing against the full class of history dependent randomized policies.
--
--   **Formalization Note** The state-only function is an existentially quantified $W(n,s)$; the theorem asserts that the history-based value $V^*_n(h_n)$ equals $W(n,s_n)$, rather than defining the value on states. Clause 2 makes explicit that the page's notation $V^\pi_n(s_n)$ for Markov policies is well defined. Rewards are bounded and the sets $\mathcal A_n(s)$, $\mathcal P_n(s,a)$ are nonempty (see the model definition); the sets $\mathcal P_n(s,a)$ need not be convex, and no supremum or infimum is assumed to be attained.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 7, Theorem 2 (Markov optimality), eq. (16)

import Mathlib
import Definitions.Def_RobustDP_FiniteHorizon_Value

namespace RobustDP.FiniteHorizon

/-- Theorem 2 (Markov optimality) (Iyengar, TR-2002-07, p. 7). There is a function
`W(n, s)` (the state-only robust value `V*_n(s)`) such that:
1. for all `n = 0, …, N`, `V*_n(h_n) = W(n, s_n)`: the robust value is a function of the current
   state alone;
2. for `n ∈ T`, the robust value `V^π_n(h_n)` of a deterministic Markov policy depends on `h_n`
   only through `s_n` (so `V^π_n(s_n)` is well defined), and `W(n, s_n) = sup_{π ∈ Π_{MD}} V^π_n(s_n)`;
3. for `n ∈ T`, the robust Bellman equation reduces to (16):
   `W(n, s) = sup_{a ∈ A(s)} inf_{p ∈ P_n(s, a)} E^p[r_n(s, a, s') + W(n + 1, s')]`. -/
theorem theorem2_markov_optimality {S A : Type*} [Countable S] [Countable A] (M : AMDP S A) :
    ∃ W : ℕ → S → ℝ,
      (∀ n ≤ M.N, ∀ h : History S A n, Vstar M n h = W n h.cur) ∧
      (∀ n < M.N, ∀ π : Policy M, IsDetMarkov π →
        ∀ h h' : History S A n, h.cur = h'.cur → V M π n h = V M π n h') ∧
      (∀ n < M.N, ∀ h : History S A n,
        W n h.cur = ⨆ π : {π : Policy M // IsDetMarkov π}, V M π.1 n h) ∧
      (∀ n < M.N, ∀ s : S,
        W n s =
          ⨆ a : M.Aset n s,
            ⨅ p : M.P n s a, expect (p : PMF S) (fun s' => M.r n s a s' + W (n + 1) s')) := by sorry

end RobustDP.FiniteHorizon
