-- Prove2me | Theorems.Thm_PoWMining_CapacityStatics_proposition_4_8
-- name    : PoWMining.CapacityStatics.proposition_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:36.20167+00:00
-- url     : https://prove2.me/theorems/97ca29ba-d650-433d-a7f6-c50f23814aad
-- title:
--   Proposition 4.8, p. 20 — sensitivities of hash rates to γ and R split into direct and indirect parts; share derivatives increase in i
-- statement:
--   Consider $n\ge2$ active miners with costs-per-hash $0<c_1\le c_2\le\dots\le c_n$, mining reward $R>0$ and capacity parameter $\gamma>0$, such that all $n$ miners are active ($R - c_k H^* > 0$ for every $k$). Let $H^* = g(c,\gamma,R)$ and $h^*_i = f_i(c,\gamma,R;H^*)$ be the aggregate and individual equilibrium hash rates of (B.3), and let $\Delta^{(\gamma)}_{i,1} = \partial f_i/\partial\gamma$, $\Delta^{(\gamma)}_{i,2} = (\partial f_i/\partial g)(\partial g/\partial\gamma)$, $\Delta^{(R)}_{i,1}=\partial f_i/\partial R$, $\Delta^{(R)}_{i,2}=(\partial f_i/\partial g)(\partial g/\partial R)$ be the direct and indirect sensitivities of (B.4). Then for every active miner $i$:
--   1. $h^*_i$ is differentiable in $\gamma$, and
--   $$\frac{\partial h^*_i}{\partial\gamma} = \Delta^{(\gamma)}_{i,1}+\Delta^{(\gamma)}_{i,2},\qquad \Delta^{(\gamma)}_{i,1}<0,\qquad \Delta^{(\gamma)}_{i,2}>0 \iff \frac{h^*_i}{H^*}<\frac12;$$
--   2. $h^*_i$ is differentiable in $R$, and
--   $$\frac{\partial h^*_i}{\partial R} = \Delta^{(R)}_{i,1}+\Delta^{(R)}_{i,2} > 0,\qquad \Delta^{(R)}_{i,1}>0,\qquad \Delta^{(R)}_{i,2}<0 \iff \frac{h^*_i}{H^*}<\frac12;$$
--   3. the shares $h^*_i/H^*$ are differentiable in $\gamma$ and in $R$, and their derivatives with respect to $\gamma$ and to $R$ are increasing in $i$, for $1\le i\le n$.
--
--   A tighter capacity constraint (larger $\gamma$) and a larger reward both shift hash rate share from the larger, cheaper miners to the smaller, costlier ones: the mining reward raises every miner's hash rate, but proportionally more for the small ones, and the capacity constraint binds hardest on the large ones.
--
--   **Formalization Note** Miners are `Fin n`, 0-based: Lean miner `i` is the paper's miner $i+1$. "Increasing in $i$" is weak monotonicity (the paper's footnote 12), stated as `Monotone` on `Fin n`; it relies on the costs being sorted, which the paper assumes without loss of generality (p. 12). The proof on p. 43 says "decreasing in $i$"; the proposition says "increasing", and the displayed expressions give increasing, which is what is stated. $\gamma>0$ is not an added restriction: (B.3), through which the proposition is proved, defines $g$ only for $\gamma>0$. The sensitivities are derivatives at a fixed set of active miners (pp. 15–16): the hash rates are the (B.3) maps of the active miners' costs. The share derivatives are asserted to exist via `HasDerivAt`, so no junk value of `deriv` can make the monotonicity claim trivial.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 20, Proposition 4.8

import Mathlib
import Definitions.Def_PoWMining_CapacityStatics_ClosedForms
import Definitions.Def_PoWMining_CapacityStatics_Sensitivities

namespace PoWMining.CapacityStatics
theorem proposition_4_8 {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) :
    (∀ i, HasDerivAt (fun x => PoWMining.CostStatics.hstar c x R i) (DeltaG1 c γ R i + DeltaG2 c γ R i) γ ∧
        DeltaG1 c γ R i < 0 ∧ (0 < DeltaG2 c γ R i ↔ PoWMining.CostStatics.share c γ R i < 1 / 2)) ∧
    (∀ i, HasDerivAt (fun x => PoWMining.CostStatics.hstar c γ x i) (DeltaR1 c γ R i + DeltaR2 c γ R i) R ∧
        0 < DeltaR1 c γ R i + DeltaR2 c γ R i ∧ 0 < DeltaR1 c γ R i ∧
        (DeltaR2 c γ R i < 0 ↔ PoWMining.CostStatics.share c γ R i < 1 / 2)) ∧
    ∃ dγ dR : Fin n → ℝ,
      (∀ i, HasDerivAt (fun x => PoWMining.CostStatics.share c x R i) (dγ i) γ) ∧
      (∀ i, HasDerivAt (fun x => PoWMining.CostStatics.share c γ x i) (dR i) R) ∧
      Monotone dγ ∧ Monotone dR := by sorry
end PoWMining.CapacityStatics
