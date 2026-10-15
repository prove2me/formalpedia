-- Prove2me | Theorems.Thm_RandomPromo_TwoPoint_lemma_6_i
-- name    : RandomPromo.TwoPoint.lemma_6_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:34.214147+00:00
-- url     : https://prove2.me/theorems/f8006a5e-f802-495f-8dea-e25f14132bf7
-- title:
--   Lemma 6(i), p. 15 — if Δ_R ≥ 1, no feasible solution of (3) earns more than the optimal static price max{vL, (1 − α)vH}
-- statement:
--   Under the standing assumptions $0<c_L<v_L<v_H$, $0<c_H<v_H$, $0<\alpha<1$, let $\Delta_R=\sqrt{\alpha c_L/((1-\alpha)(v_H-v_L))}$ and suppose $\Delta_R\ge 1$. Then every finitely supported price distribution $F$ on $\mathbb R$ feasible for problem (3) satisfies
--   $$\alpha\,\mathbb E[P\mid P\le v_L]+(1-\alpha)F(v_H)\mathbb E[P\mid P\le v_H]\le \max\{v_L,(1-\alpha)v_H\},$$
--   the expected profit of the optimal static pricing policy.
--
--   When low-valuation customers are impatient relative to the valuation gap, randomizing the price cannot beat a fixed price; this is the complementary regime to Proposition 3.
--
--   **Formalization Note** The profit of an optimal static pricing policy is $\max\{v_L,(1-\alpha)v_H\}$ (p. 12); the statement writes it explicitly. Every feasible solution is bounded, since (3) has no maximizer.
-- source:
--   Chen, Hu, Wu, Intertemporal Price Discrimination via Randomized Promotions, SSRN preprint 3223844 (revision of 2022-11-16), p. 15, Lemma 6(i); static benchmark p. 12

import Mathlib
import Definitions.Def_RandomPromo_TwoPoint_Setting

namespace RandomPromo.TwoPoint
theorem lemma_6_i (M : Params) (hM : M.Standing) (h1 : 1 ≤ M.ΔR) (w : ℝ →₀ ℝ)
    (hw : IsPriceDist w) (hF : M.Feas w) :
    M.obj3 w ≤ max M.vL ((1 - M.α) * M.vH) := by sorry
end RandomPromo.TwoPoint
