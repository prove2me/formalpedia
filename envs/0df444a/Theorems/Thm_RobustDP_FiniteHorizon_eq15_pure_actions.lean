-- Prove2me | Theorems.Thm_RobustDP_FiniteHorizon_eq15_pure_actions
-- name    : RobustDP.FiniteHorizon.eq15_pure_actions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:28.913444+00:00
-- url     : https://prove2.me/theorems/bbf61a8d-c999-40e7-8fd8-54e3e233a4bc
-- title:
--   Proof of Theorem 1, eq. (15) — the robust Bellman equation over pure actions
-- statement:
--   Fix a finite horizon AMDP, an epoch $t\in\{0,\dots,N-1\}$, a state $s$, and a bounded function $W(a,s')$ of an action and a next state (in the proof of Theorem 1, $W(a,s')=V^*_{t+1}(h_t,a,s')$). For an action $a$ and a measure $p$ on next states write
--   $$
--   g(a,p)=\sum_{s'\in\mathcal S}p(s')\big[r_t(s,a,s')+W(a,s')\big].
--   $$
--   Let $q$ range over the probability measures on $\mathcal A_t(s)$, and let $(p_{sa})_a$ range over the families with $p_{sa}\in\mathcal P_t(s,a)$ for every $a\in\mathcal A_t(s)$. Then
--   $$
--   \sup_{q}\ \inf_{(p_{sa})_a}\ \sum_{a}q(a)\,g(a,p_{sa})
--   \;=\;\sup_{q}\ \sum_{a}q(a)\inf_{p\in\mathcal P_t(s,a)}g(a,p)
--   \;=\;\sup_{a\in\mathcal A_t(s)}\ \inf_{p\in\mathcal P_t(s,a)}g(a,p).
--   $$
--
--   The first equality says that the adversary may choose its measure separately for each action (Rectangularity); the second, that randomizing over actions does not raise the robust value. Together they turn the supremum over randomized decision rules into a supremum over single actions in the robust Bellman equation (11).
--
--   **Formalization Note** The statement is the one-epoch content of the display (15), with the continuation value replaced by an arbitrary bounded $W$. Suprema and infima are not assumed to be attained.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 7, proof of Theorem 1, eq. (15)

import Mathlib
import Definitions.Def_RobustDP_FiniteHorizon_Value

namespace RobustDP.FiniteHorizon

/-- Proof of Theorem 1, eq. (15) (Iyengar, TR-2002-07, p. 7): at one epoch `t < N` and state `s`,
for a bounded continuation `W(a, s')` (in the proof, `W(a, s') = V*_{n+1}(h_n, a, s')`),
randomizing over actions does not help:
`sup_q inf_{(p_{sa})_a} Σ_a q(a) E^{p_{sa}}[r_t(s,a,·) + W(a,·)]
  = sup_q Σ_a q(a) inf_{p ∈ P_t(s,a)} E^p[r_t(s,a,·) + W(a,·)]
  = sup_{a ∈ A_t(s)} inf_{p ∈ P_t(s,a)} E^p[r_t(s,a,·) + W(a,·)]`,
where `q` ranges over the probability measures on `A_t(s)` and the family `(p_{sa})_a` over
selections `p_{sa} ∈ P_t(s, a)`. -/
theorem eq15_pure_actions {S A : Type*} [Countable S] [Countable A] (M : AMDP S A)
    (t : ℕ) (ht : t < M.N) (s : S) (W : A → S → ℝ) (hW : ∃ B : ℝ, ∀ a s', |W a s'| ≤ B) :
    (⨆ q : {q : PMF A // ∀ a ∈ q.support, a ∈ M.Aset t s},
        ⨅ p : Selection M t s,
          ∑' a, (q.1 a).toReal * expect (p.1 a) (fun s' => M.r t s a s' + W a s')) =
      (⨆ q : {q : PMF A // ∀ a ∈ q.support, a ∈ M.Aset t s},
        ∑' a, (q.1 a).toReal *
          ⨅ p : M.P t s a, expect (p : PMF S) (fun s' => M.r t s a s' + W a s')) ∧
    (⨆ q : {q : PMF A // ∀ a ∈ q.support, a ∈ M.Aset t s},
        ∑' a, (q.1 a).toReal *
          ⨅ p : M.P t s a, expect (p : PMF S) (fun s' => M.r t s a s' + W a s')) =
      ⨆ a : M.Aset t s,
        ⨅ p : M.P t s a, expect (p : PMF S) (fun s' => M.r t s a s' + W a s') := by sorry

end RobustDP.FiniteHorizon
