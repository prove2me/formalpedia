-- Prove2me | Theorems.Thm_RandomPromo_TwoPoint_lemma_6_ii_b
-- name    : RandomPromo.TwoPoint.lemma_6_ii_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:31.862719+00:00
-- url     : https://prove2.me/theorems/d98e9ae7-8719-4d9c-b624-83d09d494617
-- title:
--   Lemma 6(ii)(b), p. 15 — if Δ_R < 1 and Δ_R ≥ (cH − cL)/(vH − vL), every feasible solution of (3) earns at most U2
-- statement:
--   Under the standing assumptions $0<c_L<v_L<v_H$, $0<c_H<v_H$, $0<\alpha<1$, let $\Delta_R=\sqrt{\alpha c_L/((1-\alpha)(v_H-v_L))}$ and suppose $\Delta_R<1$ and $\Delta_R\ge\frac{c_H-c_L}{v_H-v_L}$. Then every finitely supported price distribution $F$ on $\mathbb R$ feasible for problem (3) satisfies
--   $$\alpha\,\mathbb E[P\mid P\le v_L]+(1-\alpha)F(v_H)\mathbb E[P\mid P\le v_H]\le U_2=\alpha v_L+(1-\alpha)v_H-(1-\alpha)c_H-\alpha c_L\frac{v_H-v_L}{c_H-c_L}.$$
--
--   This is the second case of the upper bound, used by Proposition 3 when the incentive constraint of the high type binds before the unconstrained optimum $\Delta_R$ is reached.
--
--   **Formalization Note** "Otherwise" is the negation of the condition of (a), $\frac{c_H-c_L}{v_H-v_L}\le\Delta_R$. No hypothesis $c_L<c_H$ is added: if $c_H\le c_L$, problem (3) has no feasible solution and the statement holds vacuously.
-- source:
--   Chen, Hu, Wu, Intertemporal Price Discrimination via Randomized Promotions, SSRN preprint 3223844 (revision of 2022-11-16), p. 15, Lemma 6(ii)(b)

import Mathlib
import Definitions.Def_RandomPromo_TwoPoint_Setting

namespace RandomPromo.TwoPoint
theorem lemma_6_ii_b (M : Params) (hM : M.Standing) (h1 : M.ΔR < 1) (h2 : M.bnd ≤ M.ΔR)
    (w : ℝ →₀ ℝ) (hw : IsPriceDist w) (hF : M.Feas w) :
    M.obj3 w ≤ M.U2 := by sorry
end RandomPromo.TwoPoint
