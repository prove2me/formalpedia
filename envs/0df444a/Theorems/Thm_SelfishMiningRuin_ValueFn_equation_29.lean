-- Prove2me | Theorems.Thm_SelfishMiningRuin_ValueFn_equation_29
-- name    : SelfishMiningRuin.ValueFn.equation_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:58.913086+00:00
-- url     : https://prove2.me/theorems/e40cbda5-91ae-4f6b-a483-0a45fa10b28b
-- title:
--   Equation (29), p. 24, corrected — advanced differential system
-- statement:
--   For a miner with positive block rate $\lambda$, cost $c$, reward $b$, and mean horizon $t$, with $0<p<1$ and $0\le q\le1$, let $\widehat V_0,\widehat V_1,\widehat V_{0^*}$ be the exponential-horizon expected surpluses of the three starting states. All three vanish at initial surplus zero. At every $u>0$ they are differentiable and satisfy the corrected system
--
--   $$
--   \begin{aligned}
--   0&=c\widehat V'_0(u)+(\lambda p+t^{-1})\widehat V_0(u)-\lambda p\widehat V_1(u)-u/t,\\
--   0&=c\widehat V'_1(u)+(\lambda+t^{-1})\widehat V_1(u)-\lambda p\widehat V_0(u+2b)-\lambda(1-p)\widehat V_{0^*}(u)-u/t,\\
--   0&=c\widehat V'_{0^*}(u)+(\lambda+t^{-1})\widehat V_{0^*}(u)-\lambda p\widehat V_0(u+2b)-\lambda(1-p)q\widehat V_0(u+b)-\lambda(1-p)(1-q)\widehat V_0(u)-u/t.
--   \end{aligned}
--   $$
--
--   This system connects the stochastic value functions to the advanced differential equation used later.
--
--   **Formalization Note** The paper prints $\widehat V_{0^*}$ in the two advanced terms of the third line. The transition rule resets a fork to state $0$ after the next block, so those terms use $\widehat V_0$.
-- source:
--   Albrecher & Goffard, On the profitability of selfish blockchain mining under consideration of ruin, arXiv:2010.12577v1, p. 24, equation (29) and boundary conditions

import Mathlib
import Definitions.Def_SelfishMiningRuin_ValueFn_Model

set_option autoImplicit false

namespace SelfishMiningRuin.ValueFn

/-- Appendix A, equation (29), p. 24, corrected: after a fork the next block resets the chain to state zero, so the two advanced terms use V̂₀ rather than the printed V̂₀*. -/
theorem equation_29 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (W : ℕ → Ω → ℝ)
    (ξ ζ : ℕ → Ω → Bool) (lam c b t p q : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (hb : 0 < b) (ht : 0 < t)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hprim : Primitives P lam p q W ξ ζ) :
    let F0 := fun u => Vhat P W ξ ζ c b u t St.zero
    let F1 := fun u => Vhat P W ξ ζ c b u t St.one
    let Ff := fun u => Vhat P W ξ ζ c b u t St.fork
    F0 0 = 0 ∧ F1 0 = 0 ∧ Ff 0 = 0 ∧
    ∀ u : ℝ, 0 < u →
      (HasDerivAt F0 (deriv F0 u) u ∧
       HasDerivAt F1 (deriv F1 u) u ∧
       HasDerivAt Ff (deriv Ff u) u) ∧
      0 = c*deriv F0 u + (lam*p + 1/t)*F0 u - lam*p*F1 u - u/t ∧
      0 = c*deriv F1 u + (lam + 1/t)*F1 u - lam*p*F0 (u+2*b) -
        lam*(1-p)*Ff u - u/t ∧
      0 = c*deriv Ff u + (lam + 1/t)*Ff u - lam*p*F0 (u+2*b) -
        lam*(1-p)*q*F0 (u+b) - lam*(1-p)*(1-q)*F0 u - u/t := by sorry

end SelfishMiningRuin.ValueFn
