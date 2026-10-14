-- Prove2me | Theorems.Thm_RoundRobinEq_SubmodularEF1_lemma_4_7
-- name    : RoundRobinEq.SubmodularEF1.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:27.107838+00:00
-- url     : https://prove2.me/theorems/13490d45-309d-4c34-ab99-2f62b453198a
-- title:
--   Lemma 4.7 — every agent gets at most 2(r − 1) goods of S′_{r−1} ∖ S′_0 in Round-Robin(≻)
-- statement:
--   In the setting of Lemma 4.6 — a profile of rankings $\succ$ over $m=kn$ goods, an agent $i$, any ranking $\succ'_i$, and the sets $S'_r$ of goods allocated in steps $1,\dots,rn+i-1$ of Round-Robin$(\succ'_i,\succ_{-i})$ — let $(A_1,\dots,A_n)$ be the allocation returned by Round-Robin$(\succ)$. Then for every $r\in[k]$ and every agent $j$,
--   $$|A_j\cap(S'_{r-1}\setminus S'_0)|\ \le\ 2(r-1).$$
--
--   No agent accumulates in the equilibrium allocation more than twice its fair share of the goods that the deviation run allocates between $i$'s first and $r$-th turns. This is the bound that makes the parity split of the proof of Theorem 4.4 work.
--
--   **Formalization Note** As for Lemma 4.6, the Lean statement holds for every ranking $\tau$ in place of $\succ'_i$ and involves no valuations. With 0-based $r$ (the paper's $r-1$) it reads `(roundRobin σ j ∩ (allocBefore σ' (r*n + i) \ allocBefore σ' i)).card ≤ 2 * r` for `r < k`, where $S'_0$ is `allocBefore σ' i`.
--
--
--   **Formalization Note** Agents are `Fin n` with $n\ge1$ (0-based: the paper's agent $i$ is `i - 1`), goods a finite type $M$ with $|M| = m$, and the paper's standing simplification $m = kn$ (p. 7) is the hypothesis `hm : Fintype.card M = k * n`; the paper calls it without loss of generality (dummy goods), and that reduction is not formalized. Steps of Round-Robin are 0-based: the paper's step $(r-1)n+i$ is step `(r-1)*n + (i-1)`, and the paper's $S_r$, $S'_r$ (goods allocated in steps $1,\dots,rn+i-1$) are `allocBefore σ (r*n + i)` and `allocBefore (Function.update σ i τ) (r*n + i)` for the 0-based agent `i`. A ranking is a duplicate-free list of all goods; the deviating profile $(\succ'_i,\succ_{-i})$ is `Function.update σ i τ`.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 19, Lemma 4.7

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularEF1_Setting

namespace RoundRobinEq.SubmodularEF1

/-- Lemma 4.7, p. 19, for an arbitrary deviation `τ` of agent `i`: every agent `j` receives in
Round-Robin(σ) at most `2r` goods of `S′_r \ S′_0` for every `r < k` (the paper's
`|A_j ∩ (S′_{r−1} \ S′_0)| ≤ 2(r − 1)`, `r ∈ [k]`). -/
theorem lemma_4_7 {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]
    (k : ℕ) (hm : Fintype.card M = k * n)
    (σ : Fin n → List M) (hσ : ∀ ℓ, IsRanking (σ ℓ))
    (i : Fin n) (τ : List M) (hτ : IsRanking τ) (j : Fin n) (r : ℕ) (hr : r < k) :
    (roundRobin σ j ∩
        (allocBefore (Function.update σ i τ) (r * n + i.val) \
          allocBefore (Function.update σ i τ) i.val)).card ≤ 2 * r := by sorry

end RoundRobinEq.SubmodularEF1
