-- Prove2me | Theorems.Thm_SurelyBetter_CLB_theorem2_max_rep
-- name    : SurelyBetter.CLB.theorem2_max_rep
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:17.568991+00:00
-- url     : https://prove2.me/theorems/425d08a9-d734-4fa2-a203-7cf19ab55985
-- title:
--   Proof of Theorem 2, p. 7628 — if ρ(E)+ρ(Eᶜ) ≥ 1, preferences over {E,Eᶜ}-measurable acts are represented by the maximum of two linear functionals
-- statement:
--   Let $S$ be a finite set of states and let $U\subseteq\mathbb R$ be a convex set containing two distinct points; $U$ stands for $u(X)$, the range of a nonconstant affine utility $u$ on simple lotteries. Acts are represented by their utility profiles $v:S\to U$ (see the definitions item for why this is exact). Let $V$ be a c-linearly biseparable preference with capacity $\rho$: $V$ is normalized, monotone and continuous on $U^S$, and for every event $E$ the functional $W(xEy)=u(x)\rho(E)+u(y)(1-\rho(E))$, $x\succsim y$, represents $V$ on all binary acts. Fix an event $E\subseteq S$ and write $E^c$ for its complement.
--
--   Suppose $\rho(E)+\rho(E^c)\ge1$. Then on $\{E,E^c\}$-measurable acts, i.e. profiles $h$ equal to $a=u(h(E))$ on $E$ and $b=u(h(E^c))$ off $E$, the preference is represented by
--   $$M(a,b)=\max\{\rho(E)\,a+(1-\rho(E))\,b,\ (1-\rho(E^c))\,a+\rho(E^c)\,b\}:$$
--   for all $a,b,a',b'\in U$, $h\precsim h'$ iff $M(a,b)\le M(a',b')$.
--
--   This convex piecewise-linear representation is the first step of the converse direction of Theorem 2.
--
--   **Formalization Note** Acts are utility profiles `S → ℝ` with values in `U`; the hypotheses `Convex ℝ U` and `∃ a ∈ U, ∃ b ∈ U, a ≠ b` encode that $U=u(X)$ for a nonconstant affine $u$, and `IsCLinBisep U V ρ` bundles the standing MBA restriction of §4 with the representation (7) as an order equivalence over binary acts of all events.
-- source:
--   Ghili & Klibanoff, If It Is Surely Better, Do It More? Implications for Preferences Under Ambiguity, Management Science 67(12) (2021), p. 7628, proof of Theorem 2 (max-representation)

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model

namespace SurelyBetter.CLB
theorem theorem2_max_rep {S : Type*} [Fintype S] (U : Set ℝ) (hU : Convex ℝ U)
    (hU2 : ∃ a ∈ U, ∃ b ∈ U, a ≠ b) (V : (S → ℝ) → ℝ) (ρ : Set S → ℝ)
    (hV : IsCLinBisep U V ρ) (E : Set S) (hρ : 1 ≤ ρ E + ρ Eᶜ) :
    ∀ a ∈ U, ∀ b ∈ U, ∀ a' ∈ U, ∀ b' ∈ U,
      (V (binProf E a b) ≤ V (binProf E a' b') ↔
        max (ρ E * a + (1 - ρ E) * b) ((1 - ρ Eᶜ) * a + ρ Eᶜ * b) ≤
          max (ρ E * a' + (1 - ρ E) * b') ((1 - ρ Eᶜ) * a' + ρ Eᶜ * b')) := by sorry
end SurelyBetter.CLB
