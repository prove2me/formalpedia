-- Prove2me | Theorems.Thm_SurelyBetter_CLB_theorem2_interior_optimum
-- name    : SurelyBetter.CLB.theorem2_interior_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:26.942633+00:00
-- url     : https://prove2.me/theorems/38498575-abe6-482f-aa20-d56f8ba38db7
-- title:
--   Proof of Theorem 2, p. 7627 — for f = xEy, g = wEz with the slope in the window, the unique optimal mixture is α* = 1/(1 + (u(x)−u(y))/(u(z)−u(w)))
-- statement:
--   Let $S$ be a finite set of states and let $U\subseteq\mathbb R$ be a convex set containing two distinct points; $U$ stands for $u(X)$, the range of a nonconstant affine utility $u$ on simple lotteries. Acts are represented by their utility profiles $v:S\to U$ (see the definitions item for why this is exact). Let $V$ be a c-linearly biseparable preference with capacity $\rho$: $V$ is normalized, monotone and continuous on $U^S$, and for every event $E$ the functional $W(xEy)=u(x)\rho(E)+u(y)(1-\rho(E))$, $x\succsim y$, represents $V$ on all binary acts. Fix an event $E\subseteq S$ and write $E^c$ for its complement.
--
--   Suppose $\rho(E)+\rho(E^c)<1$. Let $x,y,w,z\in U$ (utilities of prizes) with $x>y$, $z>w$, $x>w$, $z>y$, and let $f$ be the bet paying $x$ on $E$ and $y$ off $E$, $g$ the bet paying $w$ on $E$ and $z$ off $E$. Suppose the slope of the segment between the two profiles lies strictly inside the window given by the two linear pieces:
--   $$\frac{1-\rho(E^c)}{\rho(E^c)}\ >\ \frac{z-y}{x-w}\ >\ \frac{\rho(E)}{1-\rho(E)}.$$
--   Then the set of optimal mixtures $\alpha^*_{f,g}$ — all $\alpha\in[0,1]$ such that $\alpha f+(1-\alpha)g$ is optimal in $\{\beta f+(1-\beta)g:\beta\in[0,1]\}$ — is the single point
--   $$\alpha^*_{f,g}=\left\{\frac{1}{1+\frac{x-y}{z-w}}\right\},$$
--   the interior weight that equalizes utility across $E$ and $E^c$.
--
--   **Formalization Note** Acts are utility profiles `S → ℝ` with values in `U`; the hypotheses `Convex ℝ U` and `∃ a ∈ U, ∃ b ∈ U, a ≠ b` encode that $U=u(X)$ for a nonconstant affine $u$, and `IsCLinBisep U V ρ` bundles the standing MBA restriction of §4 with the representation (7) as an order equivalence over binary acts of all events. The slope window is stated cross-multiplied, $\rho(E)(x-w)<(1-\rho(E))(z-y)$ and $\rho(E^c)(z-y)<(1-\rho(E^c))(x-w)$, because $\rho(E^c)=0$ is allowed; then the left fraction is $+\infty$ and the second inequality reduces to $x>w$. The paper's existence remark (such $x,y,w,z$ exist) is not part of this statement.
-- source:
--   Ghili & Klibanoff, If It Is Surely Better, Do It More? Implications for Preferences Under Ambiguity, Management Science 67(12) (2021), p. 7627, proof of Theorem 2 (interior optimal mixture α*)

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model

namespace SurelyBetter.CLB
theorem theorem2_interior_optimum {S : Type*} [Fintype S] (U : Set ℝ)
    (hU : Convex ℝ U) (hU2 : ∃ a ∈ U, ∃ b ∈ U, a ≠ b) (V : (S → ℝ) → ℝ) (ρ : Set S → ℝ)
    (hV : IsCLinBisep U V ρ) (E : Set S) (hρ : ρ E + ρ Eᶜ < 1)
    (x y w z : ℝ) (hx : x ∈ U) (hy : y ∈ U) (hw : w ∈ U) (hz : z ∈ U)
    (hxy : y < x) (hzw : w < z) (hxw : w < x) (hzy : y < z)
    (hslope_lo : ρ E * (x - w) < (1 - ρ E) * (z - y))
    (hslope_hi : ρ Eᶜ * (z - y) < (1 - ρ Eᶜ) * (x - w)) :
    optMix V (binProf E x y) (binProf E w z) = {1 / (1 + (x - y) / (z - w))} := by sorry
end SurelyBetter.CLB
