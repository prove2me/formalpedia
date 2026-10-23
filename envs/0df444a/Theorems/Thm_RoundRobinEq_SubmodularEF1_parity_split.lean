-- Prove2me | Theorems.Thm_RoundRobinEq_SubmodularEF1_parity_split
-- name    : RoundRobinEq.SubmodularEF1.parity_split
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:34.326322+00:00
-- url     : https://prove2.me/theorems/5792a46b-18d9-439e-9cd9-f30757e7a614
-- title:
--   §4.2, proof of Theorem 4.4 — Y_1 and Y_2 each contain at most r − 1 goods of S′_{r−1} ∖ S′_0
-- statement:
--   Let $\succ$ be a profile of rankings over $m=kn$ goods, $i$ an agent, $\succ'_i$ any ranking, and $S'_r$ ($0\le r\le k-1$) the goods allocated in steps $1,\dots,rn+i-1$ of Round-Robin$(\succ'_i,\succ_{-i})$. Let $j\ne i$ be another agent, $A_j$ its bundle in Round-Robin$(\succ)$, and write $A_j=\{y_1,\dots,y_k\}$ with the goods indexed in the order in which they are allocated in Round-Robin$(\succ'_i,\succ_{-i})$. Split $A_j\setminus\{y_1\}$ into
--   $$Y_1=\{y_3,y_5,\dots\},\qquad Y_2=\{y_2,y_4,\dots\}.$$
--   Then for every $r\in[k]$,
--   $$\Big|\,|Y_1\cap(S'_{r-1}\setminus S'_0)|-|Y_2\cap(S'_{r-1}\setminus S'_0)|\,\Big|\le 1,$$
--   and each of $Y_1$, $Y_2$ contains at most $r-1$ goods of $S'_{r-1}\setminus S'_0$.
--
--   This is the counting step of the proof of Theorem 4.4: together with the greedy choice of agent $i$'s deviation it yields inequality (2).
--
--   **Formalization Note** The enumeration is a function `y : ℕ → M` with `IsTimeOrderedEnum σ' (roundRobin σ j) k y`: `y 0, …, y (k-1)` lists $A_j$ without repetition, and a good with a larger index is never allocated earlier in Round-Robin$(\sigma')$. The paper's $y_a$ is `y (a-1)`, so $Y_1$ is `Yone y k` (0-based indices $2,4,\dots$) and $Y_2$ is `Ytwo y k` (0-based indices $1,3,\dots$). With 0-based $r$ (the paper's $r-1$) the bounds read `≤ r` for `r < k`, and the difference is taken in $\mathbb Z$. The statement holds for every ranking $\tau$ in place of $\succ'_i$ and involves no valuations.
--
--
--   **Formalization Note** Agents are `Fin n` with $n\ge1$ (0-based: the paper's agent $i$ is `i - 1`), goods a finite type $M$ with $|M| = m$, and the paper's standing simplification $m = kn$ (p. 7) is the hypothesis `hm : Fintype.card M = k * n`; the paper calls it without loss of generality (dummy goods), and that reduction is not formalized. Steps of Round-Robin are 0-based: the paper's step $(r-1)n+i$ is step `(r-1)*n + (i-1)`, and the paper's $S_r$, $S'_r$ (goods allocated in steps $1,\dots,rn+i-1$) are `allocBefore σ (r*n + i)` and `allocBefore (Function.update σ i τ) (r*n + i)` for the 0-based agent `i`. A ranking is a duplicate-free list of all goods; the deviating profile $(\succ'_i,\succ_{-i})$ is `Function.update σ i τ`.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 20, proof of Theorem 4.4, second paragraph

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularEF1_Setting

namespace RoundRobinEq.SubmodularEF1

/-- §4.2, p. 20, proof of Theorem 4.4 (parity split), for an arbitrary deviation `τ` of agent `i`:
list `A_j` (`j ≠ i`) as `y 0, …, y (k−1)` in order of allocation in Round-Robin(τ, σ_{−i}) and split
`A_j \ {y 0}` into `Y_1` (`y 2, y 4, …`) and `Y_2` (`y 1, y 3, …`). Then for every `r < k` the numbers
of goods of `Y_1` and of `Y_2` in `S′_r \ S′_0` differ by at most one and are each at most `r`
(the paper's `r − 1` for `S′_{r−1}`, `r ∈ [k]`). -/
theorem parity_split {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]
    (k : ℕ) (hm : Fintype.card M = k * n)
    (σ : Fin n → List M) (hσ : ∀ ℓ, IsRanking (σ ℓ))
    (i : Fin n) (τ : List M) (hτ : IsRanking τ) (j : Fin n) (hji : j ≠ i)
    (y : ℕ → M) (hy : IsTimeOrderedEnum (Function.update σ i τ) (roundRobin σ j) k y)
    (r : ℕ) (hr : r < k) :
    let D := allocBefore (Function.update σ i τ) (r * n + i.val) \
      allocBefore (Function.update σ i τ) i.val
    |((Yone y k ∩ D).card : ℤ) - ((Ytwo y k ∩ D).card : ℤ)| ≤ 1 ∧
      (Yone y k ∩ D).card ≤ r ∧ (Ytwo y k ∩ D).card ≤ r := by sorry

end RoundRobinEq.SubmodularEF1
