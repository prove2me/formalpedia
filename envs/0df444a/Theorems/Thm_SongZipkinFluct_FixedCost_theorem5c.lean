-- Prove2me | Theorems.Thm_SongZipkinFluct_FixedCost_theorem5c
-- name    : SongZipkinFluct.FixedCost.theorem5c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:08.680184+00:00
-- url     : https://prove2.me/theorems/1f531841-19ef-40d5-bfad-14cacca77990
-- title:
--   Theorem 5(c) — limit points (r*(i), S*(i)) of (r*_n(i), S*_n(i)) exist and are (r, S) parameters for G_∞
-- statement:
--   In the fixed-cost model (standing hypotheses, $\alpha\bar c < p$, $K > 0$, $W_0 = W_\infty$ of the linear model), let $S^*_n(i)$, $r^*_n(i)$ ($n\ge1$) be the parameters of Theorem 3(b). For every world state $i$ the sequence $\{(r^*_n(i), S^*_n(i))\}_n$ has limit points, and if $(r^*(i), S^*(i))$ is any such limit point, then $S^*(i)$ minimizes $G_\infty(i, y)$ and
--   $$
--   G_\infty(i, r^*(i)) > K + G_\infty(i, S^*(i)),
--   $$
--   $$
--   G_\infty(i, x) \le K + G_\infty(i, S^*(i)),\qquad r^*(i) < x \le S^*(i).
--   $$
--
--   It identifies the limiting parameters as an $(r, S)$ rule for the infinite-horizon function $G_\infty$, the step from the finite-stage policies to the infinite-horizon one.
--
--   **Formalization Note** The sequence takes integer values, so a limit point is a pair taken for infinitely many $n$; the sequence itself need not converge.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 359, Theorem 5(c)

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Bounds

open Filter Topology

namespace SongZipkinFluct.FixedCost

open Model

/-- Theorem 5(c) (p. 359) of Song and Zipkin (1993). Fixed-cost model of §3.2
(`K = K̄F̃_L(α) > 0`, `W₀ = W_∞` of the linear model). Let `S*_n(i)`, `r*_n(i)` (`n ≥ 1`) be the
parameters of Theorem 3(b). For every `i`, the sequence `n ↦ (r*_n(i), S*_n(i))` has limit
points, and for any limit point `(r*(i), S*(i))`: `S*(i)` minimizes `G_∞(i, ·)`,
`G_∞(i, r*(i)) > K + G_∞(i, S*(i))`, and `G_∞(i, x) ≤ K + G_∞(i, S*(i))` for
`r*(i) < x ≤ S*(i)`.

Formalization Note: the sequence is integer-valued, so a limit point is a pair taken by the
sequence for infinitely many `n` (`∃ᶠ n in atTop`); the sequence need not converge. -/
theorem theorem5c {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (hK : 0 < M.Kbar)
    (rs Ss : ℕ → I → ℤ) (hrs : IsStageParams M rs Ss) (i : I) :
    (∃ r S : ℤ, ∃ᶠ n in atTop, rs n i = r ∧ Ss n i = S) ∧
      ∀ r S : ℤ, (∃ᶠ n in atTop, rs n i = r ∧ Ss n i = S) →
        (∀ y : ℤ, GinfK M i S ≤ GinfK M i y) ∧
        M.K + GinfK M i S < GinfK M i r ∧
        ∀ x : ℤ, r < x → x ≤ S → GinfK M i x ≤ M.K + GinfK M i S := by sorry

end SongZipkinFluct.FixedCost
