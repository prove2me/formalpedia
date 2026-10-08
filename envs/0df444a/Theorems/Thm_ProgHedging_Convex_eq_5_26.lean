-- Prove2me | Theorems.Thm_ProgHedging_Convex_eq_5_26
-- name    : ProgHedging.Convex.eq_5_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:50.938983+00:00
-- url     : https://prove2.me/theorems/bfe2cbb1-6ae0-496a-b616-0604a3b2b24a
-- title:
--   (5.26) — one exact iteration is firmly nonexpansive in ‖·‖_r on 𝒩 × ℳ (proof of Theorem 5.1)
-- statement:
--   Assume the convex case and $r>0$. Let $(V,W),(V',W')\in\mathcal N\times\mathcal M$, and let one exact iteration of progressive hedging take $(V,W)$ to $(V_1,W_1)$ and $(V',W')$ to $(V_1',W_1')$. Then
--
--   $$
--   \|(V_1',W_1')-(V_1,W_1)\|_r^2+\bigl\|\bigl((V',W')-(V_1',W_1')\bigr)-\bigl((V,W)-(V_1,W_1)\bigr)\bigr\|_r^2\le\|(V',W')-(V,W)\|_r^2,
--   $$
--
--   where $\|(X,W)\|_r=(\|X\|^2+r^{-2}\|W\|^2)^{1/2}$.
--
--   This is the firm nonexpansiveness of the iteration map, from which the monotonicity statements (5.3) and (5.4) of Theorem 5.1 follow.
--
--   **Formalization Note.** The paper states (5.26) for $M_r=(I+T_r)^{-1}$ acting on $Z=(V,\bar W)$ with $\bar W=r^{-1}W$, in the norm $\|(V,\bar W)\|=(\|V\|^2+\|\bar W\|^2)^{1/2}$. By (5.5)–(5.7) and (5.22), $M_r(V,r^{-1}W)=(V_1,r^{-1}W_1)$ exactly when one exact iteration takes $(V,W)$ to $(V_1,W_1)$, and $\|(X,\bar W)\|=\|(X,W)\|_r$; the statement above is (5.26) in these original variables. The operator $T_r$ itself is not introduced.
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), p. 23, (5.26) in the proof of Theorem 5.1, with (5.5)–(5.7) p. 21 and (5.22)–(5.23)

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Convex_Algorithm
open scoped RealInnerProductSpace Pointwise Topology
open Filter

namespace ProgHedging.Convex

/-- (5.26), proof of Theorem 5.1, p. 23, in the original variables. In the convex case with
`r > 0`, let one exact iteration take `(V, W) ∈ 𝒩 × ℳ` to `(V₁, W₁)` and `(V', W') ∈ 𝒩 × ℳ` to
`(V₁', W₁')`. Then, in the norm `‖·‖_r` of (5.2),
`‖(V₁', W₁') − (V₁, W₁)‖_r² + ‖((V', W') − (V₁', W₁')) − ((V, W) − (V₁, W₁))‖_r² ≤ ‖(V', W') − (V, W)‖_r²`. -/
theorem eq_5_26 {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (hconv : pr.ConvexCase) {r : ℝ} (hr : 0 < r)
    (V W V' W' V₁ W₁ V₁' W₁' : Policy S n)
    (hV : V ∈ pr.N) (hW : W ∈ pr.M) (hV' : V' ∈ pr.N) (hW' : W' ∈ pr.M)
    (hstep : pr.IsStep r V W V₁ W₁) (hstep' : pr.IsStep r V' W' V₁' W₁') :
    pr.rnorm r (V₁' - V₁) (W₁' - W₁) ^ 2 +
        pr.rnorm r ((V' - V₁') - (V - V₁)) ((W' - W₁') - (W - W₁)) ^ 2 ≤
      pr.rnorm r (V' - V) (W' - W) ^ 2 := by sorry

end ProgHedging.Convex
