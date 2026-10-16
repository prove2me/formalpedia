-- Prove2me | Theorems.Thm_StrategicAlloc_RRFair_lemma_3_5
-- name    : StrategicAlloc.RRFair.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:34.058738+00:00
-- url     : https://prove2.me/theorems/48c2c72d-f4c9-4e36-b740-4e472a2bf3a7
-- title:
--   Lemma 3.5 — a strict best responder can be replaced by a truthful one with the same allocation and the same view of it
-- statement:
--   Suppose the valuation $v_1$ of the first-moving agent induces a strict preference ranking (no two goods have the same value), and let $b=(b_1,\dots,b_n)$ be a bid profile in which $b_1$ is a best response of agent 1 to $b_{-1}=(b_2,\dots,b_n)$. Let $(A_1,\dots,A_n)$ be the allocation of Round-Robin$(b)$. Then there is a valuation function $v_1^*\ge0$ such that
--
--   1. with $b_1^*=(v_1^*(g_1),\dots,v_1^*(g_m))$ the truthful bid for $v_1^*$, Round-Robin$(b_1^*,b_{-1})$ returns the same allocation $(A_1,\dots,A_n)$;
--   2. $v_1^*(A_1)=v_1(A_1)$;
--   3. $v_1^*(g)=v_1(g)$ for every good $g\in M\setminus A_1$.
--
--   Combined with Lemma 3.1 this gives Theorem 3.4 for strict valuations: the imaginary truthful agent sees the allocation as envy-free, and she values every bundle as agent 1 does.
--
--   **Formalization Note.** Agents are `Fin n` and goods `Fin m`, both 0-based (the paper's agent $i$ is $i-1$, good $g_j$ is $j-1$, and the paper's step $t$ is $t-1$). The result is stated for Round-Robin started at an arbitrary agent $s$ on an arbitrary set $G$ of goods (`rrFrom s G`); the page states the instance $s =$ agent 1, $G = M$. The proof of Theorem 3.3 (p. 10) applies the result in this generality, to Round-Robin$_\ell$ on $M' = M\setminus H$ with agent $\ell$ "in the role of agent 1"; by p. 6 this is only a renaming of the agents. "Strict preference ranking" is injectivity of $v_s$. The valuation $v_1^*$ is required to be non-negative, as every valuation function of the model is (p. 4), so that its truthful bid is a bid. The page writes "$b_{-i}=(b_2,\dots,b_n)$" for $b_{-1}$; the statement uses $b_{-1}$.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 9, Lemma 3.5

import Mathlib
import Definitions.Def_StrategicAlloc_RRFair_Setting

namespace StrategicAlloc.RRFair

variable {n m : ℕ}

/-- Lemma 3.5 (p. 9), for Round-Robin started at agent `s` on the goods `G`: if `v s` is
injective and `b s` is a best response, there is a non-negative valuation `w` whose truthful bid
leaves the allocation unchanged, gives agent `s`'s bundle the same value, and agrees with `v s`
off agent `s`'s bundle. -/
theorem lemma_3_5 [NeZero n] (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (s : Fin n) (G : Finset (Fin m)) (b : Fin n → Fin m → ℝ) (hb : IsBidProfile b)
    (hstrict : Function.Injective (v s))
    (hbr : IsBestResponse (rrFrom s G) v b s) :
    ∃ w : Fin m → ℝ, (∀ g, 0 ≤ w g) ∧
      rrFrom s G (Function.update b s w) = rrFrom s G b ∧
      ∑ g ∈ rrFrom s G b s, w g = val v s (rrFrom s G b s) ∧
      ∀ g, g ∉ rrFrom s G b s → w g = v s g := by sorry

end StrategicAlloc.RRFair
