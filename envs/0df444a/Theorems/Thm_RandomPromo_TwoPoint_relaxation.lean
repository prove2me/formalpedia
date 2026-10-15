-- Prove2me | Theorems.Thm_RandomPromo_TwoPoint_relaxation
-- name    : RandomPromo.TwoPoint.relaxation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:30.498413+00:00
-- url     : https://prove2.me/theorems/d433eb8a-4b82-4bd4-9cd8-a642c2e8483e
-- title:
--   §3.2.2, p. 14 — for every distribution feasible for (2), E[P|P ≤ p^L] ≤ E[P|P ≤ vL], so (3) relaxes (2)
-- statement:
--   Consider the two-segment model with the standing assumptions $0<c_L<v_L<v_H$, $0<c_H<v_H$, $0<\alpha<1$. Let $P$ be a finitely supported random price on $\mathbb R$ such that low-valuation customers wait and high-valuation customers do not:
--   $$\mathbb E[(v_L-P)^+]>c_L,\qquad \mathbb E[(v_H-P)^+]\le c_H.$$
--   Let $\underline p^L=\max\{v'\mid \mathbb E[(v'-P)^+]\le c_L\}$ be the low type's purchase threshold. Then
--   $$\mathbb E[P\mid P\le \underline p^L]\le \mathbb E[P\mid P\le v_L],$$
--   and consequently the objective of problem (2) at this law is at most the objective of problem (3):
--   $$\alpha\,\mathbb E[P\mid P\le \underline p^L]+(1-\alpha)F(v_H)\mathbb E[P\mid P\le v_H]\le \alpha\,\mathbb E[P\mid P\le v_L]+(1-\alpha)F(v_H)\mathbb E[P\mid P\le v_H].$$
--
--   This is the step that replaces problem (2) by its relaxation (3): every upper bound on (3) is an upper bound on (2).
--
--   **Formalization Note** The inequality is asserted for laws feasible for (2), as on the page; for an arbitrary law it can fail. The second conjunct is the meaning of "relaxation" and follows from $\alpha>0$.
-- source:
--   Chen, Hu, Wu, Intertemporal Price Discrimination via Randomized Promotions, SSRN preprint 3223844 (revision of 2022-11-16), p. 14, §3.2.2, before (3)

import Mathlib
import Definitions.Def_RandomPromo_TwoPoint_Setting

namespace RandomPromo.TwoPoint
theorem relaxation (M : Params) (hM : M.Standing) (w : ℝ →₀ ℝ) (hw : IsPriceDist w)
    (hF : M.Feas w) :
    condExp w (thresh w M.cL) ≤ condExp w M.vL ∧ M.obj2 w ≤ M.obj3 w := by sorry
end RandomPromo.TwoPoint
