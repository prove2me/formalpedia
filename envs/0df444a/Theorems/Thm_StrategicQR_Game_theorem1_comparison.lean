-- Prove2me | Theorems.Thm_StrategicQR_Game_theorem1_comparison
-- name    : StrategicQR.Game.theorem1_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:25:26.008149+00:00
-- url     : https://prove2.me/theorems/b6a22738-7798-4449-bc67-67dd79231014
-- title:
--   Theorem 1 (ii), p. 16 — any RE equilibrium satisfies $q^*\le q^m$ and $\pi^*\le\pi^m$
-- statement:
--   Assume MSLR and no rationing, $0<\alpha\le1$ and $v_B<c<p$. Let $(q^*,v^*)$ be any rational expectations equilibrium and let $q^m\ge0$ be any maximizer of the myopic profit $\pi^m$ on $[0,\infty)$. Then
--   $$q^*\le q^m\qquad\text{and}\qquad \pi^*=\pi(q^*,v^*)\le\pi^m(q^m)=\pi^m .$$
--
--   The retailer orders less, and earns less, when some consumers are strategic: lowering inventory raises the expected markdown price and induces some strategic consumers to buy at full price.
--
--   **Formalization Note** The proof's display (5) prints $+\int_{D_m}^{D_h}(2s_h(x)-\bar v)\,dF(x)$; subtracting (2) from the myopic first-order condition gives $-\int$, so "each term in (5) is positive" is not right as printed. The conclusion survives, since $\int_{D_m}^{D_h}(2s_h-\bar v)\,dF\le p\,(F(D_h)-F(q))$. MSLR is the paper's standing assumption on demand; under it the distribution function is strictly increasing on the support, which makes the myopic maximizer unique.
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 16, Theorem 1; p. 17, proof part (ii), eq. (5)

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

namespace StrategicQR.Game

/-- Theorem 1, comparison part (p. 16; proof part (ii), p. 17). Under MSLR and no rationing, for
`0 < α ≤ 1` and `vB < c < p`, every rational expectations equilibrium `(q*, v*)` and every
maximizer `q^m` of the myopic profit `π^m` satisfy `q* ≤ q^m` and `π* = π(q*, v*) ≤ π^m(q^m)`. -/
theorem theorem1_comparison (M : Model) (hmslr : MSLR M.f) (hNR : NoRationing M) {α c : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hc : M.vB < c) (hcp : c < M.p) {q v qm : ℝ}
    (heq : IsEquilibrium M α c q v) (hqm : qm ∈ Set.Ici (0 : ℝ))
    (hmax : IsMaxOn (fun q' => profit M 0 c q' M.vhi) (Set.Ici 0) qm) :
    q ≤ qm ∧ profit M α c q v ≤ profit M 0 c qm M.vhi := by sorry

end StrategicQR.Game
