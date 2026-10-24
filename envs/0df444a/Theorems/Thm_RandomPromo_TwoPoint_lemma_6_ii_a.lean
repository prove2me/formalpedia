-- Prove2me | Theorems.Thm_RandomPromo_TwoPoint_lemma_6_ii_a
-- name    : RandomPromo.TwoPoint.lemma_6_ii_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:37.035914+00:00
-- url     : https://prove2.me/theorems/055e0bd3-339a-4398-ae4e-0ac8116a12ec
-- title:
--   Lemma 6(ii)(a), p. 15 — if Δ_R < 1 and Δ_R < (cH − cL)/(vH − vL), every feasible solution of (3) earns at most U1
-- statement:
--   Under the standing assumptions $0<c_L<v_L<v_H$, $0<c_H<v_H$, $0<\alpha<1$, let
--   $$\Delta_R=\sqrt{\frac{\alpha c_L}{(1-\alpha)(v_H-v_L)}}$$
--   and suppose $\Delta_R<1$ and $\Delta_R<\frac{c_H-c_L}{v_H-v_L}$. Then every finitely supported price distribution $F$ on $\mathbb R$ feasible for problem (3) satisfies
--   $$\alpha\,\mathbb E[P\mid P\le v_L]+(1-\alpha)F(v_H)\mathbb E[P\mid P\le v_H]\le U_1=\alpha v_L+(1-\alpha)v_H-(1-\alpha)c_L-2(1-\alpha)(v_H-v_L)\Delta_R.$$
--
--   Together with the relaxation step this bounds the optimal value of the firm's problem (2) by $U_1$; Proposition 3 shows the bound is approached.
--
--   **Formalization Note** "The optimal expected profit from (3) is no more than $U_1$" is read as a bound on every feasible solution, since (3) has no maximizer.
-- source:
--   Chen, Hu, Wu, Intertemporal Price Discrimination via Randomized Promotions, SSRN preprint 3223844 (revision of 2022-11-16), p. 15, Lemma 6(ii)(a)

import Mathlib
import Definitions.Def_RandomPromo_TwoPoint_Setting

namespace RandomPromo.TwoPoint
theorem lemma_6_ii_a (M : Params) (hM : M.Standing) (h1 : M.ΔR < 1) (h2 : M.ΔR < M.bnd)
    (w : ℝ →₀ ℝ) (hw : IsPriceDist w) (hF : M.Feas w) :
    M.obj3 w ≤ M.U1 := by sorry
end RandomPromo.TwoPoint
