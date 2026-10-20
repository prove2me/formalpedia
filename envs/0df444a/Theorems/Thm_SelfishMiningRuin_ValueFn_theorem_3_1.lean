-- Prove2me | Theorems.Thm_SelfishMiningRuin_ValueFn_theorem_3_1
-- name    : SelfishMiningRuin.ValueFn.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:27.868507+00:00
-- url     : https://prove2.me/theorems/511dc236-3b59-44d8-be89-1e2d1e0843d1
-- title:
--   Theorem 3.1, p. 11, corrected — selfish-miner expected surplus under ruin
-- statement:
--   A miner pays costs at rate $c>0$, receives $b>0$ per rewarded block, and faces network blocks at rate $\lambda>0$. The miner owns hash share $0<p<1$; in a fork, other miners extend the miner's branch with probability $0\le q\le1$. Let $t>0$ be the mean of an independent exponential evaluation horizon. The exponential-horizon expected surplus $\widehat V_0(u,t)$ starts with an empty buffer, and rewards cease at ruin.
--
--   Let $\rho_1$ and $\rho_2\pm i\rho_3$ be precisely the roots with negative real part of the characteristic equation (21), with $\rho_3\ne0$. Let $A_1,A_2,A_3$ solve the corrected linear system (23) using constants (22) and (24). Then, for every $u\ge0$,
--
--   $$
--   \widehat V_0(u,t)=A_1e^{\rho_1u}+e^{\rho_2u}\bigl(A_2\cos(\rho_3u)+A_3\sin(\rho_3u)\bigr)+u+C.
--   $$
--
--   The formula evaluates expected remaining capital for the specified withholding strategy while accounting for the possibility of ruin before the horizon.
--
--   **Formalization Note** The third right-hand side of printed (23) is corrected to $-(\lambda^2p^2/c^2)(2b+C)-1/(ct)$, as required by (33). The Poisson process is constructed from independent exponential interarrivals; the horizon is integrated against an exponential law of rate $1/t$.
-- source:
--   Albrecher & Goffard, On the profitability of selfish blockchain mining under consideration of ruin, arXiv:2010.12577v1, p. 11, Theorem 3.1, equations (19)–(24), with correction to (23)

import Mathlib
import Definitions.Def_SelfishMiningRuin_ValueFn_Model
import Definitions.Def_SelfishMiningRuin_ValueFn_Formula

set_option autoImplicit false

namespace SelfishMiningRuin.ValueFn

/-- Theorem 3.1, p. 11, corrected: equation (23)'s third right-hand side is −(λ²p²/c²)(2b+C)−1/(ct), as forced by the paper's boundary condition (33). -/
theorem theorem_3_1 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (W : ℕ → Ω → ℝ)
    (ξ ζ : ℕ → Ω → Bool) (lam c b t p q rho1 rho2 rho3 A1 A2 A3 : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (hb : 0 < b) (ht : 0 < t)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hprim : Primitives P lam p q W ξ ζ)
    (hrho3 : rho3 ≠ 0)
    (hroots : {rho : ℂ | rho.re < 0 ∧ charFun lam c b t p q rho = 0} =
      {(rho1 : ℂ), Complex.mk rho2 rho3, Complex.mk rho2 (-rho3)})
    (hA : System23 lam c b t p q rho1 rho2 rho3 A1 A2 A3) :
    ∀ u : ℝ, 0 ≤ u →
      Vhat P W ξ ζ c b u t St.zero =
        closedForm lam c b t p q rho1 rho2 rho3 A1 A2 A3 u := by sorry

end SelfishMiningRuin.ValueFn
