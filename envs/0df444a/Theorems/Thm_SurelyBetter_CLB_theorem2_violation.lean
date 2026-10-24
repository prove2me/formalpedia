-- Prove2me | Theorems.Thm_SurelyBetter_CLB_theorem2_violation
-- name    : SurelyBetter.CLB.theorem2_violation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:13.238493+00:00
-- url     : https://prove2.me/theorems/3c3b66b1-6c74-4c10-bd56-4d9542800f2e
-- title:
--   Theorem 2, first direction, p. 7627 — if ρ(E)+ρ(Eᶜ) < 1, monotonicity in optimal mixtures fails on {E,Eᶜ}-measurable acts
-- statement:
--   Let $S$ be a finite set of states and let $U\subseteq\mathbb R$ be a convex set containing two distinct points; $U$ stands for $u(X)$, the range of a nonconstant affine utility $u$ on simple lotteries. Acts are represented by their utility profiles $v:S\to U$ (see the definitions item for why this is exact). Let $V$ be a c-linearly biseparable preference with capacity $\rho$: $V$ is normalized, monotone and continuous on $U^S$, and for every event $E$ the functional $W(xEy)=u(x)\rho(E)+u(y)(1-\rho(E))$, $x\succsim y$, represents $V$ on all binary acts. Fix an event $E\subseteq S$ and write $E^c$ for its complement.
--
--   If
--   $$\rho(E)+\rho(E^c)<1,$$
--   then $V$ violates monotonicity in optimal mixtures restricted to acts measurable with respect to $\{E,E^c\}$: there are such acts $f\le f'$ (statewise) and $g$ for which the set of optimal weights on $f$ in $\{\alpha f+(1-\alpha)g\}$ is not smaller in the set order than the set of optimal weights on $f'$ in $\{\alpha f'+(1-\alpha)g\}$.
--
--   This is the incompatibility half of Theorem 2: ambiguity aversion toward a single event already rules out monotone comparative statics of optimal mixtures, for every c-linearly biseparable preference (MEU, Choquet EU, $\alpha$-MEU).
--
--   **Formalization Note** Acts are utility profiles `S → ℝ` with values in `U`; the hypotheses `Convex ℝ U` and `∃ a ∈ U, ∃ b ∈ U, a ≠ b` encode that $U=u(X)$ for a nonconstant affine $u$, and `IsCLinBisep U V ρ` bundles the standing MBA restriction of §4 with the representation (7) as an order equivalence over binary acts of all events.
-- source:
--   Ghili & Klibanoff, If It Is Surely Better, Do It More? Implications for Preferences Under Ambiguity, Management Science 67(12) (2021), p. 7627, Theorem 2 (first sentence)

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model

namespace SurelyBetter.CLB
theorem theorem2_violation {S : Type*} [Fintype S] (U : Set ℝ) (hU : Convex ℝ U)
    (hU2 : ∃ a ∈ U, ∃ b ∈ U, a ≠ b) (V : (S → ℝ) → ℝ) (ρ : Set S → ℝ)
    (hV : IsCLinBisep U V ρ) (E : Set S) :
    ρ E + ρ Eᶜ < 1 → ¬ MOMOn V (measE U E) := by sorry
end SurelyBetter.CLB
