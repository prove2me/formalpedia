-- Prove2me | Theorems.Thm_StrategicAlloc_RRFair_claim_3_8
-- name    : StrategicAlloc.RRFair.claim_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:35.655008+00:00
-- url     : https://prove2.me/theorems/9f2a32ee-ee97-408d-81d2-b10b5ff53427
-- title:
--   Claim 3.8 — at the first divergence of the two runs, the original run allocates the slid good s
-- statement:
--   Let $b$ be a bid profile and let agent $i$ change her bid to $c$, giving $b'=(c,b_{-i})$, where the ranking $\succ'_i$ induced by $c$ is within a partial slide of the ranking $\succ_i$ induced by $b_i$: writing $q_1\succ_i\dots\succ_i q_m$, for some $x<y$ the ranking $\succ'_i$ is $\succ_i$ with $q_x$ moved to just after $q_y$. Let $s=q_x$ be the slid good. Suppose $t^*$ is the first step at which the good $\gamma$ allocated by Round-Robin$(b)$ differs from the good $\gamma'$ allocated by Round-Robin$(b')$. Then
--   $$\gamma = s.$$
--
--   This rules out the one configuration in the induction of Lemma 3.7 that could make the available sets drift apart.
--
--   **Formalization Note.** Agents are `Fin n` and goods `Fin m`, both 0-based (the paper's agent $i$ is $i-1$, good $g_j$ is $j-1$, and the paper's step $t$ is $t-1$). The result is stated for Round-Robin started at an arbitrary agent $s$ on an arbitrary set $G$ of goods (`rrFrom s G`); the page states the instance $s =$ agent 1, $G = M$. The proof of Theorem 3.3 (p. 10) applies the result in this generality, to Round-Robin$_\ell$ on $M' = M\setminus H$ with agent $\ell$ "in the role of agent 1"; by p. 6 this is only a renaming of the agents. The slide is given by explicit positions $x<y$ (0-based) with `rank c = ((rank (b i)).eraseIdx x).insertIdx y q_x`, and $s$ is `(rank (b i))[x]`. "First divergence at $t$" is `pick … b t ≠ pick … b' t` together with agreement at every earlier step; the conclusion is `pick … b t = some s`. Bids are non-negative as on p. 5.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 11, Claim 3.8 (and the sentence before it defining s)

import Mathlib
import Definitions.Def_StrategicAlloc_RRFair_Setting

namespace StrategicAlloc.RRFair

variable {n m : ℕ}

/-- Claim 3.8 (p. 11): agent `i` changes her bid from `b i` to `c`, and the ranking of `c` is
the ranking of `b i` with its `x`-th good `s = (rank (b i))[x]` slid down to just after the
`y`-th good. At the first step `t` where the two runs allocate different goods, the original
run allocates `s`. -/
theorem claim_3_8 [NeZero n] (s₀ : Fin n) (G : Finset (Fin m)) (b : Fin n → Fin m → ℝ)
    (hb : IsBidProfile b) (i : Fin n) (c : Fin m → ℝ) (hc : ∀ g, 0 ≤ c g)
    (x y : ℕ) (hx : x < (rank (b i)).length) (hxy : x < y) (hy : y < (rank (b i)).length)
    (hslide : rank c = ((rank (b i)).eraseIdx x).insertIdx y ((rank (b i))[x]))
    (t : ℕ) (hne : pick s₀ G b t ≠ pick s₀ G (Function.update b i c) t)
    (hfirst : ∀ t' < t, pick s₀ G b t' = pick s₀ G (Function.update b i c) t') :
    pick s₀ G b t = some ((rank (b i))[x]) := by sorry

end StrategicAlloc.RRFair
