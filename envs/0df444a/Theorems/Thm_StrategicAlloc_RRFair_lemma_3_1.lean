-- Prove2me | Theorems.Thm_StrategicAlloc_RRFair_lemma_3_1
-- name    : StrategicAlloc.RRFair.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:31.409744+00:00
-- url     : https://prove2.me/theorems/474b17f0-7cc8-4e15-97bf-55b8e60f3404
-- title:
--   Lemma 3.1 — a truthful bidder sees Round-Robin's allocation as EF1, and as EF if she picks first
-- statement:
--   Let $v_1,\dots,v_n$ be non-negative additive valuations and $b$ a bid profile, and let $(A_1,\dots,A_n)$ be the allocation returned by Round-Robin. If agent $i$ bids truthfully, $b_i=(v_i(g_1),\dots,v_i(g_m))$, then the allocation is EF1 from her perspective:
--   $$\forall j\in N\text{ with }A_j\neq\emptyset\ \ \exists g\in A_j:\quad v_i(A_i)\ \ge\ v_i(A_j\setminus\{g\}).$$
--   Moreover, if $i$ is the agent who picks first, the allocation is EF from her perspective: $v_i(A_i)\ge v_i(A_j)$ for all $j\in N$.
--
--   The other agents' bids are arbitrary. This is the classical fairness guarantee of Round-Robin (Markakis, Theorem 12.2 of *Trends in Computational Social Choice*), seen from a single truthful agent; the "Moreover" part is what makes the first mover's best response envy-free in Theorem 3.4.
--
--   **Formalization Note.** Agents are `Fin n` and goods `Fin m`, both 0-based (the paper's agent $i$ is $i-1$, good $g_j$ is $j-1$, and the paper's step $t$ is $t-1$). The result is stated for Round-Robin started at an arbitrary agent $s$ on an arbitrary set $G$ of goods (`rrFrom s G`); the page states the instance $s =$ agent 1, $G = M$. The proof of Theorem 3.3 (p. 10) applies the result in this generality, to Round-Robin$_\ell$ on $M' = M\setminus H$ with agent $\ell$ "in the role of agent 1"; by p. 6 this is only a renaming of the agents. Ties among the truthful bids are broken by the mechanism's lexicographic rule.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 7, Lemma 3.1

import Mathlib
import Definitions.Def_StrategicAlloc_RRFair_Setting

namespace StrategicAlloc.RRFair

variable {n m : ℕ}

/-- Lemma 3.1 (p. 7), for Round-Robin started at agent `s` on the goods `G` (the page is
`s = 0`, `G = univ`): if agent `i` bids truthfully, the allocation is EF1 from her
perspective, and EF from her perspective if she picks first. -/
theorem lemma_3_1 [NeZero n] (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (s : Fin n) (G : Finset (Fin m)) (b : Fin n → Fin m → ℝ) (hb : IsBidProfile b)
    (i : Fin n) (hi : b i = v i) :
    IsEF1For v (rrFrom s G b) i ∧ (i = s → IsEFFor v (rrFrom s G b) i) := by sorry

end StrategicAlloc.RRFair
