-- Prove2me | Theorems.Thm_SelfishMiningRuin_ValueFn_Vhat_linear_bound
-- name    : SelfishMiningRuin.ValueFn.Vhat_linear_bound
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T08:30:37.394977+00:00
-- url     : https://prove2.me/theorems/98c2ef9d-af79-40ee-9766-0e5ea1fbe866
-- title:
--   Linear growth and continuity at zero of the exponential-horizon value functions
-- statement:
--   Fix a cost rate $c>0$, a block reward $b>0$, a network block rate $\lambda>0$, a mean exponential horizon $t>0$, a hash share $0<p<1$ and a fork-support probability $0\le q\le 1$, and let the interarrival times and marks have the joint law described by `Primitives`. For a starting state $z\in\{0,1,0^*\}$ let $\widehat V_z(u,t)$ be the exponential-horizon expected surplus under ruin (equation (19)).
--
--   Then there is a constant $K$ such that for every state $z$ and every initial surplus $u\ge 0$,
--
--   $$
--   \bigl|\widehat V_z(u,t)\bigr|\le K\,u .
--   $$
--
--   This packages the two analytic properties of the value functions that the paper uses without proof when it passes from the advanced differential system (29) to the explicit formula (20): the **linear growth condition** in $u$ (p. 25, which rules out the exponential modes with positive real part), and the fact that the boundary values $\widehat V_z(0,t)=0$ in (30) are attained continuously, i.e. $\widehat V_z(u,t)\to 0$ as $u\downarrow 0$.
--
--   **Formalization Note** A single bound $|\widehat V_z(u,t)|\le Ku$ on $u\ge0$ encodes both properties at once; the constant $K$ may depend on all the model parameters.
-- source:
--   Albrecher & Goffard, On the profitability of selfish blockchain mining under consideration of ruin, arXiv:2010.12577v1, Appendix A, p. 25 (linear growth condition for V̂0(u,t) in u) and boundary conditions (30), p. 24

import Mathlib
import Definitions.Def_SelfishMiningRuin_ValueFn_Model

set_option autoImplicit false

namespace SelfishMiningRuin.ValueFn

/-- Linear growth of the exponential-horizon value functions, with vanishing at zero surplus
(p. 25 and boundary conditions (30)): `|V̂_z(u,t)| ≤ K u` for all `u ≥ 0` and all states. -/
theorem Vhat_linear_bound {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (W : ℕ → Ω → ℝ)
    (ξ ζ : ℕ → Ω → Bool) (lam c b t p q : ℝ)
    (hlam : 0 < lam) (hc : 0 < c) (hb : 0 < b) (ht : 0 < t)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hprim : Primitives P lam p q W ξ ζ) :
    ∃ K : ℝ, ∀ z : St, ∀ u : ℝ, 0 ≤ u → |Vhat P W ξ ζ c b u t z| ≤ K * u := by sorry

end SelfishMiningRuin.ValueFn
