-- Prove2me | Theorems.Thm_SurelyBetter_CLB_theorem2_converse
-- name    : SurelyBetter.CLB.theorem2_converse
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:17.774552+00:00
-- url     : https://prove2.me/theorems/3db4e1f4-b9c5-4f95-a849-4ec0d4a89bab
-- title:
--   Theorem 2, converse, pp. 7627–7628 — if ρ(E)+ρ(Eᶜ) ≥ 1 and max{ρ(E),ρ(Eᶜ)} < 1 or min{ρ(E),ρ(Eᶜ)} = 0, MOM holds on {E,Eᶜ}-measurable acts
-- statement:
--   Let $S$ be a finite set of states and let $U\subseteq\mathbb R$ be a convex set containing two distinct points; $U$ stands for $u(X)$, the range of a nonconstant affine utility $u$ on simple lotteries. Acts are represented by their utility profiles $v:S\to U$ (see the definitions item for why this is exact). Let $V$ be a c-linearly biseparable preference with capacity $\rho$: $V$ is normalized, monotone and continuous on $U^S$, and for every event $E$ the functional $W(xEy)=u(x)\rho(E)+u(y)(1-\rho(E))$, $x\succsim y$, represents $V$ on all binary acts. Fix an event $E\subseteq S$ and write $E^c$ for its complement.
--
--   Suppose that either $\max\{\rho(E),\rho(E^c)\}<1$ or $\min\{\rho(E),\rho(E^c)\}=0$. If
--   $$\rho(E)+\rho(E^c)\ge1,$$
--   then $V$ satisfies monotonicity in optimal mixtures restricted to acts measurable with respect to $\{E,E^c\}$: for all such acts $f,f',g$ with $f\le f'$ statewise, the set of optimal weights on $f$ in $\{\alpha f+(1-\alpha)g:\alpha\in[0,1]\}$ is smaller in the set order (Definition 1) than the set of optimal weights on $f'$ in $\{\alpha f'+(1-\alpha)g:\alpha\in[0,1]\}$.
--
--   This is the converse half of Theorem 2. Remark 2 of the paper ($\rho(E)=1$, $\rho(E^c)=1/2$) shows that the side condition cannot be dropped.
--
--   **Formalization Note** Acts are utility profiles `S → ℝ` with values in `U`; the hypotheses `Convex ℝ U` and `∃ a ∈ U, ∃ b ∈ U, a ≠ b` encode that $U=u(X)$ for a nonconstant affine $u$, and `IsCLinBisep U V ρ` bundles the standing MBA restriction of §4 with the representation (7) as an order equivalence over binary acts of all events.
-- source:
--   Ghili & Klibanoff, If It Is Surely Better, Do It More? Implications for Preferences Under Ambiguity, Management Science 67(12) (2021), pp. 7627–7628, Theorem 2 (second sentence) and its proof

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model

namespace SurelyBetter.CLB
theorem theorem2_converse {S : Type*} [Fintype S] (U : Set ℝ) (hU : Convex ℝ U)
    (hU2 : ∃ a ∈ U, ∃ b ∈ U, a ≠ b) (V : (S → ℝ) → ℝ) (ρ : Set S → ℝ)
    (hV : IsCLinBisep U V ρ) (E : Set S) :
    (max (ρ E) (ρ Eᶜ) < 1 ∨ min (ρ E) (ρ Eᶜ) = 0) → 1 ≤ ρ E + ρ Eᶜ →
      MOMOn V (measE U E) := by sorry
end SurelyBetter.CLB
