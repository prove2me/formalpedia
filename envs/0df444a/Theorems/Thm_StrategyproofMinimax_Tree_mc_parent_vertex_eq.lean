-- Prove2me | Theorems.Thm_StrategyproofMinimax_Tree_mc_parent_vertex_eq
-- name    : StrategyproofMinimax.Tree.mc_parent_vertex_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T22:25:24.016115+00:00
-- url     : https://prove2.me/theorems/81fbc150-fe3d-46c4-9fb4-c3aca6967b1e
-- title:
--   Appendix B, p. 526 — under xᵏ the facility at lᵏ⁻¹ has maximum cost 2ᵏ⁻¹
-- statement:
--   Let $k\ge1$, $n\ge1$ and let $2m^k$ divide $n$. For every path $l^0,l^1,\dots,l^{k-1}$ of left vertices, the deterministic facility at $l^{k-1}$ has maximum cost exactly $2^{k-1}$ under the profile $x^k$ built along that path:
--   $$\operatorname{mc}\big(\delta_{l^{k-1}},x^k\big)=\max_{i\in N} d\big(x^k_i,l^{k-1}\big)=2^{k-1}.$$
--   Hence $\mathrm{OPT}(x^k)\le 2^{k-1}$, the denominator of the ratio in the proof of Theorem 4.1.
--
--   **Formalization Note.** The path is the word $v=(l^1,\dots,l^{k-1})$ of length $k-1$, $l^{k-1}$ is `vertex .left v`, and $x^k$ is `profileAlong m k n v`.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 526, Appendix B

import Mathlib
import Definitions.Def_StrategyproofMinimax_Tree_cost
import Definitions.Def_StrategyproofMinimax_Tree_HardTree
import Definitions.Def_StrategyproofMinimax_Tree_profileAlong

namespace StrategyproofMinimax.Tree

/-- Appendix B, p. 526: under `xᵏ` (built along the path `l⁰, …, lᵏ⁻¹`, the word `v` of length
`k − 1`), the deterministic solution that locates the facility at `lᵏ⁻¹` has maximum cost
`2ᵏ⁻¹`. -/
theorem mc_parent_vertex_eq {m k n : ℕ} (hk : 1 ≤ k) (hn : 0 < n) (hdiv : 2 * m ^ k ∣ n)
    (v : List (Fin m)) (hv : v.length = k - 1) :
    mc (diracPM (vertex .left v : HardTree m k)) (profileAlong m k n v) =
      (2 : ℝ) ^ (k - 1) := by sorry

end StrategyproofMinimax.Tree
