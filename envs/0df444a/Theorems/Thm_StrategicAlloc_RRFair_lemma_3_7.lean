-- Prove2me | Theorems.Thm_StrategicAlloc_RRFair_lemma_3_7
-- name    : StrategicAlloc.RRFair.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:14.35169+00:00
-- url     : https://prove2.me/theorems/a0723ab0-9a62-45f1-998e-e175b99d4a5f
-- title:
--   Lemma 3.7 — a partial slide changes the available goods by at most one good at every step
-- statement:
--   Let $b$ be a bid profile and $b'=(b_i',b_{-i})$, where the rankings $\succ_i$ and $\succ'_i$ induced by $b_i$ and $b_i'$ are within a partial slide of each other. Then for every $t\in[m+1]$
--   $$|M_t(b)\setminus M_t(b')| \;=\; |M_t(b')\setminus M_t(b)| \;\le\; 1,$$
--   where $M_t(b)$ is the set of goods still available right after $t-1$ goods have been allocated by Round-Robin$(b)$.
--
--   Moving one good down a single agent's ranking can change the allocation drastically, but the two runs never have more than one unallocated good not shared by the other. The lemma drives the recursive construction in the proof of Lemma 3.5.
--
--   **Formalization Note.** Agents are `Fin n` and goods `Fin m`, both 0-based (the paper's agent $i$ is $i-1$, good $g_j$ is $j-1$, and the paper's step $t$ is $t-1$). The result is stated for Round-Robin started at an arbitrary agent $s$ on an arbitrary set $G$ of goods (`rrFrom s G`); the page states the instance $s =$ agent 1, $G = M$. The proof of Theorem 3.3 (p. 10) applies the result in this generality, to Round-Robin$_\ell$ on $M' = M\setminus H$ with agent $\ell$ "in the role of agent 1"; by p. 6 this is only a renaming of the agents. With 0-based steps the range $t\in[m+1]$ becomes $t\in\{0,\dots,|G|\}$ and $M_{t+1}(b)$ is `avail s₀ G b t`. Bids are non-negative as on p. 5.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 11, Lemma 3.7 (Definition 3.6, p. 10)

import Mathlib
import Definitions.Def_StrategicAlloc_RRFair_Setting

namespace StrategicAlloc.RRFair

variable {n m : ℕ}

/-- Lemma 3.7 (p. 11): if agent `i`'s ranking under `c` is within a partial slide of her ranking
under `b i`, then at every step `t = 0, …, |G|` the sets of available goods of the two runs
differ by at most one good on each side, and by the same number on both sides. -/
theorem lemma_3_7 [NeZero n] (s₀ : Fin n) (G : Finset (Fin m)) (b : Fin n → Fin m → ℝ)
    (hb : IsBidProfile b) (i : Fin n) (c : Fin m → ℝ) (hc : ∀ g, 0 ≤ c g)
    (hslide : IsPartialSlide (rank (b i)) (rank c)) :
    ∀ t ≤ G.card,
      (avail s₀ G b t \ avail s₀ G (Function.update b i c) t).card =
          (avail s₀ G (Function.update b i c) t \ avail s₀ G b t).card ∧
        (avail s₀ G b t \ avail s₀ G (Function.update b i c) t).card ≤ 1 := by sorry

end StrategicAlloc.RRFair
