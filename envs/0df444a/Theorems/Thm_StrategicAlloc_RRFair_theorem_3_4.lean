-- Prove2me | Theorems.Thm_StrategicAlloc_RRFair_theorem_3_4
-- name    : StrategicAlloc.RRFair.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:43.493343+00:00
-- url     : https://prove2.me/theorems/e29e2770-cfe4-4065-8b9c-52a76c4491c5
-- title:
--   Theorem 3.4 — a best-responding first mover envies no bundle of Round-Robin's allocation
-- statement:
--   Let $v_1,\dots,v_n$ be non-negative additive valuations and $b$ a bid profile in which the bid $b_1$ of agent 1 is a best response to the fixed bids $b_2,\dots,b_n$. Then agent 1 does not envy any bundle of the allocation $(A_1,\dots,A_n)$ returned by Round-Robin$(b)$:
--   $$v_1(A_1)\ \ge\ v_1(A_j)\qquad\text{for every } j\in N.$$
--
--   Theorem 3.3 follows by applying this to each agent $\ell$ in the role of the first mover of a restricted run.
--
--   **Formalization Note.** Agents are `Fin n` and goods `Fin m`, both 0-based (the paper's agent $i$ is $i-1$, good $g_j$ is $j-1$, and the paper's step $t$ is $t-1$). The result is stated for Round-Robin started at an arbitrary agent $s$ on an arbitrary set $G$ of goods (`rrFrom s G`); the page states the instance $s =$ agent 1, $G = M$. The proof of Theorem 3.3 (p. 10) applies the result in this generality, to Round-Robin$_\ell$ on $M' = M\setminus H$ with agent $\ell$ "in the role of agent 1"; by p. 6 this is only a renaming of the agents. No strictness is assumed on $v$: the complete proof (pp. 24–25) treats ties through Lemma A.1.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 9, Theorem 3.4 (complete proof pp. 24–25)

import Mathlib
import Definitions.Def_StrategicAlloc_RRFair_Setting

namespace StrategicAlloc.RRFair

variable {n m : ℕ}

/-- Theorem 3.4 (p. 9), for Round-Robin started at agent `s` on the goods `G`: if the first
mover `s` bids a best response, she envies no bundle (with respect to `v s`). -/
theorem theorem_3_4 [NeZero n] (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (s : Fin n) (G : Finset (Fin m)) (b : Fin n → Fin m → ℝ) (hb : IsBidProfile b)
    (hbr : IsBestResponse (rrFrom s G) v b s) :
    IsEFFor v (rrFrom s G b) s := by sorry

end StrategicAlloc.RRFair
