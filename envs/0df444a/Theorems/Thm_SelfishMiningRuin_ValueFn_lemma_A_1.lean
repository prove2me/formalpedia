-- Prove2me | Theorems.Thm_SelfishMiningRuin_ValueFn_lemma_A_1
-- name    : SelfishMiningRuin.ValueFn.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:13.917632+00:00
-- url     : https://prove2.me/theorems/428e5269-2cfb-4e57-8c55-4ea052570c6f
-- title:
--   Lemma A.1, p. 26 — three left-half-plane characteristic roots
-- statement:
--   Let $\lambda,c,b,t>0$ and $0<p,q<1$. Form the characteristic equation (35) with the coefficients $D_1,\ldots,D_7$ defined in (22). Its set of complex roots with strictly negative real part has exactly three elements, and exactly one of those roots is real.
--
--   $$
--   \#\{\rho\in\mathbb C:\operatorname{Re}\rho<0,\ (D_1\rho+D_2)e^{2b\rho}+D_3e^{b\rho}=D_4\rho^3+D_5\rho^2+D_6\rho+D_7\}=3.
--   $$
--
--   This count identifies the roots appearing in Theorem 3.1 and shows that its root description is nonvacuous for the lemma's parameter range.
-- source:
--   Albrecher & Goffard, On the profitability of selfish blockchain mining under consideration of ruin, arXiv:2010.12577v1, p. 26, Lemma A.1 (equation (35))

import Mathlib
import Definitions.Def_SelfishMiningRuin_ValueFn_Formula

set_option autoImplicit false

namespace SelfishMiningRuin.ValueFn

/-- Lemma A.1, p. 26: the characteristic equation has exactly three roots in the open left half-plane, exactly one of them real. -/
theorem lemma_A_1 (lam c b t p q : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (hb : 0 < b) (ht : 0 < t)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    let roots := {rho : ℂ | rho.re < 0 ∧ charFun lam c b t p q rho = 0}
    roots.ncard = 3 ∧ ∃! rho : ℂ, rho ∈ roots ∧ rho.im = 0 := by sorry

end SelfishMiningRuin.ValueFn
