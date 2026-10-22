-- Prove2me | Theorems.Thm_StrategyproofMinimax_Tree_sp_approx_ratio_ge_two_sub
-- name    : StrategyproofMinimax.Tree.sp_approx_ratio_ge_two_sub
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T22:27:36.329341+00:00
-- url     : https://prove2.me/theorems/cc6f5a7f-0da7-4d30-8061-112d7af861b0
-- title:
--   Theorem 4.1 — no strategyproof randomized mechanism on the tree G(m, k) beats ratio 2 − 1/2ᵏ − 4/m for the minimax
-- statement:
--   Let $m\ge2$, $k\ge1$ and $n\ge1$ with $2m^k$ dividing $n$, and let $G=G(m,k)$ be the tree of Appendix B. For every strategyproof randomized mechanism $f:G^n\to\Delta(G)$ there is a location profile $x\in G^n$ with $\mathrm{OPT}(x)>0$ and
--   $$\operatorname{mc}(f(x),x)\ \ge\ \Big(2-\frac1{2^k}-\frac4m\Big)\cdot\mathrm{OPT}(x),\qquad \mathrm{OPT}(x)=\min_{z\in G}\operatorname{mc}(\delta_z,x).$$
--   In particular no strategyproof randomized mechanism on $G(m,k)$ has an approximation ratio for the minimax smaller than $2-1/2^k-4/m$.
--
--   This is the paper's Theorem 4.1: the paper writes that there is a tree on which no SP randomized mechanism has approximation ratio smaller than $2-O(1/2^{\sqrt{\log n}})$. Its proof yields $2-1/2^k-4/m$ on $G(m,k)$ (p. 526), and the choice $k=\Theta(\sqrt{\log n})$, $m=\Theta(n^{1/k})$ gives the $O(\cdot)$ form. Together with the mechanism of Section 4 (ratio $2-2/(n+2)$ on every tree), it shows that on trees randomization cannot improve on the ratio $2$ of dictatorship by more than a vanishing amount.
--
--   **Formalization Note.** The paper's $O(\cdot)$ is replaced by the explicit bound its proof establishes, $2-1/2^k-4/m$, and the paper's "assume for ease of exposition that $2m^k$ divides $n$" is the hypothesis `2 * m ^ k ∣ n`. The mechanism is any function `(Fin n → HardTree m k) → ProbabilityMeasure (HardTree m k)` that is SP against every unilateral deviation to any point of the tree; no measurability, anonymity or continuity is assumed. The clause $\mathrm{OPT}(x)>0$ rules out the trivial witness (a profile with all agents at one point, for which both sides vanish), so the inequality is a genuine ratio bound.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 518, Theorem 4.1; explicit bound p. 526, Appendix B

import Mathlib
import Definitions.Def_StrategyproofMinimax_Tree_cost
import Definitions.Def_StrategyproofMinimax_Tree_HardTree

namespace StrategyproofMinimax.Tree

/-- Theorem 4.1 (p. 518) in the explicit form its proof establishes (p. 526): on the tree
`G(m, k)` of Appendix B, with `m ≥ 2`, `k ≥ 1` and `2mᵏ ∣ n`, every strategyproof randomized
mechanism `f` for `n` agents has a profile `x` with `OPT(x) > 0` and
`mc(f(x), x) ≥ (2 − 1/2ᵏ − 4/m) · OPT(x)`, so its approximation ratio for the minimax is at least
`2 − 1/2ᵏ − 4/m`. The paper writes `2 − O(1/2^√(log n))`, obtained with `k = Θ(√(log n))` and
`m = Θ(n^(1/k))`. -/
theorem sp_approx_ratio_ge_two_sub {m k n : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k) (hn : 0 < n)
    (hdiv : 2 * m ^ k ∣ n)
    (f : (Fin n → HardTree m k) → MeasureTheory.ProbabilityMeasure (HardTree m k))
    (hf : IsStrategyproof f) :
    ∃ x : Fin n → HardTree m k, 0 < optMc x ∧
      (2 - 1 / (2 : ℝ) ^ k - 4 / (m : ℝ)) * optMc x ≤ mc (f x) x := by sorry

end StrategyproofMinimax.Tree
