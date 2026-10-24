-- Prove2me | Theorems.Thm_RoundRobinEq_SubmodularEF1_closing_bound
-- name    : RoundRobinEq.SubmodularEF1.closing_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:38.738381+00:00
-- url     : https://prove2.me/theorems/85da52d2-2566-4102-9c49-1c050f8dadb7
-- title:
--   §4.2, proof of Theorem 4.4 — v_i(A_j ∖ {y_1}) ≤ 3/α · v_i(A_i), with y_1 the first good of A_j in the deviation run
-- statement:
--   Let $\alpha\in(0,1]$, let all agents have non-decreasing, normalized, submodular valuations $v_1,\dots,v_n$ over $m=kn$ goods, and let $\succ$ be an $\alpha$-approximate pure Nash equilibrium of Round-Robin with allocation $(A_1,\dots,A_n)$. Fix an agent $i$, a greedy response $\succ'_i$ of $i$ to $\succ_{-i}$ (Algorithm 4), and an agent $j\ne i$, and let $y_1$ be the good of $A_j$ allocated first in Round-Robin$(\succ'_i,\succ_{-i})$. Then
--   $$v_i(A_j\setminus\{y_1\})\ \le\ \frac{3}{\alpha}\cdot v_i(A_i).$$
--
--   This is the conclusion of the proof of Theorem 4.4: it exhibits $y_1$ as the good whose removal makes $j$'s bundle at most $3/\alpha$ times as valuable to $i$ as $i$'s own.
--
--   **Formalization Note** The bound is stated in the page's form $v_i(A_j\setminus\{y_1\})\le (3/\alpha)\,v_i(A_i)$, equivalent to $(\alpha/3)\,v_i(A_j\setminus\{y_1\})\le v_i(A_i)$ for $\alpha>0$. $y_1$ is `y 0` for a time-ordered enumeration `y` of $A_j$ in the deviation run (`IsTimeOrderedEnum`); when $k=0$ the bundle is empty and the statement is trivially true. The greedy response is encoded relationally (`IsGreedyResponse`), covering every tie-breaking of Algorithm 4.
--
--
--   **Formalization Note** Agents are `Fin n` with $n\ge1$ (0-based: the paper's agent $i$ is `i - 1`), goods a finite type $M$ with $|M| = m$, and the paper's standing simplification $m = kn$ (p. 7) is the hypothesis `hm : Fintype.card M = k * n`; the paper calls it without loss of generality (dummy goods), and that reduction is not formalized. Steps of Round-Robin are 0-based: the paper's step $(r-1)n+i$ is step `(r-1)*n + (i-1)`, and the paper's $S_r$, $S'_r$ (goods allocated in steps $1,\dots,rn+i-1$) are `allocBefore σ (r*n + i)` and `allocBefore (Function.update σ i τ) (r*n + i)` for the 0-based agent `i`. A ranking is a duplicate-free list of all goods; the deviating profile $(\succ'_i,\succ_{-i})$ is `Function.update σ i τ`.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, pp. 20–21, proof of Theorem 4.4, closing display

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularEF1_Setting

namespace RoundRobinEq.SubmodularEF1

/-- §4.2, pp. 20–21, proof of Theorem 4.4 (closing bound): for submodular valuations, an
`α`-approximate PNE `σ`, a greedy response `τ` (Algorithm 4) of agent `i` to `σ_{−i}`, and `j ≠ i`,
with `y 0` the good of `A_j` allocated first in Round-Robin(τ, σ_{−i}):
`v_i(A_j \ {y 0}) ≤ (3/α) · v_i(A_i)`. -/
theorem closing_bound {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M]
    (k : ℕ) (hm : Fintype.card M = k * n) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (v : Fin n → Finset M → ℝ) (hv : ∀ i, IsValuation (v i)) (hsub : ∀ i, IsSubmodular (v i))
    (σ : Fin n → List M) (hσ : IsApproxPNE α v σ)
    (i j : Fin n) (hji : j ≠ i) (τ : List M) (hτ : IsGreedyResponse (v i) σ i τ)
    (y : ℕ → M) (hy : IsTimeOrderedEnum (Function.update σ i τ) (roundRobin σ j) k y) :
    v i ((roundRobin σ j).erase (y 0)) ≤ 3 / α * v i (roundRobin σ i) := by sorry

end RoundRobinEq.SubmodularEF1
