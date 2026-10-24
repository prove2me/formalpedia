-- Prove2me | Theorems.Thm_RoundRobinEq_SubmodularEF1_inequality_2
-- name    : RoundRobinEq.SubmodularEF1.inequality_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:29.701459+00:00
-- url     : https://prove2.me/theorems/2904a4d3-73c8-459d-85ad-67a7c0a67727
-- title:
--   Inequality (2) — the greedy deviation dominates each Algorithm 3-renamed good of Y_ℓ marginally
-- statement:
--   Let $\succ$ be a profile of rankings over $m=kn$ goods, $i$ an agent with valuation $v_i$, and $\succ'_i$ a greedy response of $i$ to $\succ_{-i}$ (Algorithm 4). Let $x_r$ be the good agent $i$ receives in round $r$ of Round-Robin$(\succ'_i,\succ_{-i})$, so that $A'_i=\{x_1,\dots,x_k\}$. For an agent $j\ne i$ list its bundle $A_j$ in Round-Robin$(\succ)$ as $y_1,\dots,y_k$ in order of allocation in Round-Robin$(\succ'_i,\succ_{-i})$, form $Y_1=\{y_3,y_5,\dots\}$ and $Y_2=\{y_2,y_4,\dots\}$, and for $\ell\in\{1,2\}$ rename $Y_\ell=\{y^\ell_1,\dots,y^\ell_{\tau_\ell}\}$ by Algorithm 3 with inputs $A'_i$, $Y_\ell$, $v_i$. Then for $\ell\in\{1,2\}$ and $r\in[\tau_\ell]$,
--   $$v_i(x_r\mid\{x_1,\dots,x_{r-1}\})\ \ge\ v_i(y^\ell_r\mid\{x_1,\dots,x_{r-1}\}).\tag{2}$$
--
--   Inequality (2) is the good-by-good comparison that, summed over $r$ and combined with submodularity, bounds $v_i(A_j\setminus\{y_1\})$ by three times $v_i(A'_i)$ in the closing bound.
--
--   **Formalization Note** The greedy response and Algorithm 3 are encoded relationally (`IsGreedyResponse`, `IsAlg3Order`), so the statement covers every tie-breaking. The hypothesis `hx` identifies `x r` (0-based round `r`) with the good picked at step `r*n + i` of the deviation run, and `Y` is either `Yone y k` or `Ytwo y k`. No equilibrium hypothesis and no property of $v_i$ is assumed: the argument of p. 20 uses only the greedy choice, the Algorithm 3 order and the parity split, so the Lean statement holds for an arbitrary real set function $v_i$, which is stronger than the paper's setting. 0-based: `y' r` is the paper's $y^\ell_{r+1}$ and `(Finset.range r).image x` is $\{x_1,\dots,x_r\}$ in the paper's indexing, i.e. the goods $i$ received before its $(r+1)$-st pick.
--
--
--   **Formalization Note** Agents are `Fin n` with $n\ge1$ (0-based: the paper's agent $i$ is `i - 1`), goods a finite type $M$ with $|M| = m$, and the paper's standing simplification $m = kn$ (p. 7) is the hypothesis `hm : Fintype.card M = k * n`; the paper calls it without loss of generality (dummy goods), and that reduction is not formalized. Steps of Round-Robin are 0-based: the paper's step $(r-1)n+i$ is step `(r-1)*n + (i-1)`, and the paper's $S_r$, $S'_r$ (goods allocated in steps $1,\dots,rn+i-1$) are `allocBefore σ (r*n + i)` and `allocBefore (Function.update σ i τ) (r*n + i)` for the 0-based agent `i`. A ranking is a duplicate-free list of all goods; the deviating profile $(\succ'_i,\succ_{-i})$ is `Function.update σ i τ`.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 20, proof of Theorem 4.4, inequality (2)

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularEF1_Setting

namespace RoundRobinEq.SubmodularEF1

/-- Inequality (2), p. 20: let `τ` be a greedy response (Algorithm 4) of agent `i` with valuation
`vi` to `σ_{−i}`, `x r` the good agent `i` receives in round `r` (0-based) of Round-Robin(τ, σ_{−i}),
`y` the allocation-time enumeration of `A_j` (`j ≠ i`) in that run, `Y` one of `Y_1, Y_2`, and `y′`
an Algorithm 3 ordering of `Y` with respect to `x`. Then for every `r < |Y|`,
`v_i(x_r | {x_0, …, x_{r−1}}) ≥ v_i(y′_r | {x_0, …, x_{r−1}})`. -/
theorem inequality_2 {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]
    (k : ℕ) (hm : Fintype.card M = k * n)
    (σ : Fin n → List M) (hσ : ∀ ℓ, IsRanking (σ ℓ))
    (i j : Fin n) (hji : j ≠ i) (vi : Finset M → ℝ)
    (τ : List M) (hτ : IsGreedyResponse vi σ i τ)
    (x : ℕ → M) (hx : ∀ r < k, pick (Function.update σ i τ) (r * n + i.val) = some (x r))
    (y : ℕ → M) (hy : IsTimeOrderedEnum (Function.update σ i τ) (roundRobin σ j) k y)
    (Y : Finset M) (hY : Y = Yone y k ∨ Y = Ytwo y k)
    (y' : ℕ → M) (hy' : IsAlg3Order vi x Y y') :
    ∀ r < Y.card,
      marginal vi {y' r} ((Finset.range r).image x) ≤
        marginal vi {x r} ((Finset.range r).image x) := by sorry

end RoundRobinEq.SubmodularEF1
