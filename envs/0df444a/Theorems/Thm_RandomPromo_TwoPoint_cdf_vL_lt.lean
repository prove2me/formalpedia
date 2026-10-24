-- Prove2me | Theorems.Thm_RandomPromo_TwoPoint_cdf_vL_lt
-- name    : RandomPromo.TwoPoint.cdf_vL_lt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:35.787029+00:00
-- url     : https://prove2.me/theorems/529e2cfa-bc24-4139-b0ce-13841f68dc4b
-- title:
--   §3.2.2, p. 14 — every feasible solution of (3) has F(vL) < (cH − cL)/(vH − vL)
-- statement:
--   Under the standing assumptions $0<c_L<v_L<v_H$, $0<c_H<v_H$, $0<\alpha<1$, let $P$ be a finitely supported random price on $\mathbb R$ with distribution function $F$ that is feasible for problem (3):
--   $$\mathbb E[(v_L-P)^+]>c_L,\qquad \mathbb E[(v_H-P)^+]\le c_H.$$
--   Then
--   $$F(v_L)<\frac{c_H-c_L}{v_H-v_L}.$$
--
--   The bound confines the probability $\beta=F(v_L)$ of a price at most $v_L$, which is the variable over which the upper bounds of Lemma 6 are optimized.
--
--   **Formalization Note** No hypothesis $c_L<c_H$ is assumed. When $c_H\le c_L$ the conclusion says that no feasible law exists.
-- source:
--   Chen, Hu, Wu, Intertemporal Price Discrimination via Randomized Promotions, SSRN preprint 3223844 (revision of 2022-11-16), p. 14, §3.2.2, after (3)

import Mathlib
import Definitions.Def_RandomPromo_TwoPoint_Setting

namespace RandomPromo.TwoPoint
theorem cdf_vL_lt (M : Params) (hM : M.Standing) (w : ℝ →₀ ℝ) (hw : IsPriceDist w)
    (hF : M.Feas w) :
    cdf w M.vL < (M.cH - M.cL) / (M.vH - M.vL) := by sorry
end RandomPromo.TwoPoint
