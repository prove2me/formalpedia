-- Prove2me | Theorems.Thm_RoundRobinEq_SubmodularEF1_lemma_4_6
-- name    : RoundRobinEq.SubmodularEF1.lemma_4_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:34.812191+00:00
-- url     : https://prove2.me/theorems/305d619e-2e51-4d19-a823-47c63a485c4a
-- title:
--   Lemma 4.6 — a deviation of agent i changes at most r − 1 of the goods allocated before i's r-th pick
-- statement:
--   Let $\succ=(\succ_1,\dots,\succ_n)$ be a profile of rankings over $m=kn$ goods, fix an agent $i$ and any ranking $\succ'_i$. For $0\le r\le k-1$ let $S_r$ and $S'_r$ be the sets of goods allocated in steps $1,\dots,rn+i-1$ of Round-Robin$(\succ)$ and of Round-Robin$(\succ'_i,\succ_{-i})$, i.e. the goods allocated right before agent $i$ receives a good in round $r+1$. Then for every $r\in[k]$,
--   $$|S'_{r-1}\setminus S_{r-1}|\ \le\ r-1 .$$
--
--   That is, right before agent $i$'s $r$-th pick in Round-Robin$(\succ)$, at most $r-1$ goods of $S'_{r-1}$ are still unallocated: a unilateral deviation shifts only a $1/n$ fraction of the goods allocated up to any of $i$'s turns. With Lemma 4.7 it controls how the deviation redistributes goods among the other agents, and it serves both the submodular case (Theorem 4.4) and the cancelable case (Theorem 4.5).
--
--   **Formalization Note** The paper states the lemma for the specific deviation $\succ'_i$ of each case (Algorithm 4's output, or a strict version of $i$'s true ranking), but its proof never uses how $\succ'_i$ was chosen; the Lean statement holds for every ranking $\tau$, which contains both cases. No valuations appear. With 0-based $r$ (the paper's $r-1$), the statement reads `(allocBefore σ' (r*n + i) \ allocBefore σ (r*n + i)).card ≤ r` for `r < k`.
--
--
--   **Formalization Note** Agents are `Fin n` with $n\ge1$ (0-based: the paper's agent $i$ is `i - 1`), goods a finite type $M$ with $|M| = m$, and the paper's standing simplification $m = kn$ (p. 7) is the hypothesis `hm : Fintype.card M = k * n`; the paper calls it without loss of generality (dummy goods), and that reduction is not formalized. Steps of Round-Robin are 0-based: the paper's step $(r-1)n+i$ is step `(r-1)*n + (i-1)`, and the paper's $S_r$, $S'_r$ (goods allocated in steps $1,\dots,rn+i-1$) are `allocBefore σ (r*n + i)` and `allocBefore (Function.update σ i τ) (r*n + i)` for the 0-based agent `i`. A ranking is a duplicate-free list of all goods; the deviating profile $(\succ'_i,\succ_{-i})$ is `Function.update σ i τ`.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 19, Lemma 4.6 (notation S_r, S′_r on p. 19)

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularEF1_Setting

namespace RoundRobinEq.SubmodularEF1

/-- Lemma 4.6, p. 19, for an arbitrary deviation `τ` of agent `i`: with `S_r` / `S′_r` the goods
allocated in the (0-based) steps before step `r * n + i` of Round-Robin(σ) / Round-Robin(τ, σ_{−i}),
`|S′_r \ S_r| ≤ r` for every `r < k` (the paper's `|S′_{r−1} \ S_{r−1}| ≤ r − 1`, `r ∈ [k]`). -/
theorem lemma_4_6 {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]
    (k : ℕ) (hm : Fintype.card M = k * n)
    (σ : Fin n → List M) (hσ : ∀ ℓ, IsRanking (σ ℓ))
    (i : Fin n) (τ : List M) (hτ : IsRanking τ) (r : ℕ) (hr : r < k) :
    (allocBefore (Function.update σ i τ) (r * n + i.val) \ allocBefore σ (r * n + i.val)).card
      ≤ r := by sorry

end RoundRobinEq.SubmodularEF1
