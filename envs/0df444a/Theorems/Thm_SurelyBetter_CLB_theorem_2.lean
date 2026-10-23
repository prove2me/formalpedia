-- Prove2me | Theorems.Thm_SurelyBetter_CLB_theorem_2
-- name    : SurelyBetter.CLB.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:12.608611+00:00
-- url     : https://prove2.me/theorems/55358896-59a1-4ac1-b9ae-fae7f47e205e
-- title:
--   Theorem 2, p. 7627 — ρ(E)+ρ(Eᶜ) < 1 violates monotonicity in optimal mixtures on {E,Eᶜ}-measurable acts; the converse holds if max{ρ(E),ρ(Eᶜ)} < 1 or min{ρ(E),ρ(Eᶜ)} = 0
-- statement:
--   Let $S$ be a finite set of states and let $U\subseteq\mathbb R$ be a convex set containing two distinct points; $U$ stands for $u(X)$, the range of a nonconstant affine utility $u$ on simple lotteries. Acts are represented by their utility profiles $v:S\to U$ (see the definitions item for why this is exact). Let $V$ be a c-linearly biseparable preference with capacity $\rho$: $V$ is normalized, monotone and continuous on $U^S$, and for every event $E$ the functional $W(xEy)=u(x)\rho(E)+u(y)(1-\rho(E))$, $x\succsim y$, represents $V$ on all binary acts. Fix an event $E\subseteq S$ and write $E^c$ for its complement.
--
--   Then:
--
--   1. If $\rho(E)+\rho(E^c)<1$, $V$ violates monotonicity in optimal mixtures restricted to acts measurable with respect to $\{E,E^c\}$.
--   2. If $\max\{\rho(E),\rho(E^c)\}<1$ or $\min\{\rho(E),\rho(E^c)\}=0$, and
--   $$\rho(E)+\rho(E^c)\ge1,$$
--   then $V$ satisfies monotonicity in optimal mixtures restricted to acts measurable with respect to $\{E,E^c\}$.
--
--   Here monotonicity in optimal mixtures restricted to a set $\mathcal G$ of acts means: for all $f,f',g\in\mathcal G$ with $f'(s)\succsim f(s)$ for every state $s$, the set of $\alpha^*\in[0,1]$ such that $\alpha^*f+(1-\alpha^*)g$ is optimal in $\{\alpha f+(1-\alpha)g:\alpha\in[0,1]\}$ is smaller in the set order (Definition 1: $A\le_s B$ iff $a\in A$, $b\in B$ imply $\min\{a,b\}\in A$, $\max\{a,b\}\in B$) than the corresponding set for $f'$ and $g$.
--
--   The quantity $\rho(E)+\rho(E^c)$ classifies the attitude toward bets on $E$: below $1$ is ambiguity aversion, $1$ neutrality, above $1$ ambiguity loving. The theorem says that, for the c-linearly biseparable class (which includes maxmin expected utility, Choquet expected utility and $\alpha$-MEU), ambiguity aversion toward even a single event is incompatible with monotonicity in optimal mixtures, while (under the side condition) ambiguity neutrality or loving toward the event is compatible with it.
--
--   **Formalization Note** Acts are utility profiles `S → ℝ` with values in `U`; the hypotheses `Convex ℝ U` and `∃ a ∈ U, ∃ b ∈ U, a ≠ b` encode that $U=u(X)$ for a nonconstant affine $u$, and `IsCLinBisep U V ρ` bundles the standing MBA restriction of §4 with the representation (7) as an order equivalence over binary acts of all events. "The converse" is read, as in the paper's proof, as: $\rho(E)+\rho(E^c)\ge1$ implies the property.
-- source:
--   Ghili & Klibanoff, If It Is Surely Better, Do It More? Implications for Preferences Under Ambiguity, Management Science 67(12) (2021), p. 7627, Theorem 2

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model

namespace SurelyBetter.CLB
theorem theorem_2 {S : Type*} [Fintype S] (U : Set ℝ) (hU : Convex ℝ U)
    (hU2 : ∃ a ∈ U, ∃ b ∈ U, a ≠ b) (V : (S → ℝ) → ℝ) (ρ : Set S → ℝ)
    (hV : IsCLinBisep U V ρ) (E : Set S) :
    (ρ E + ρ Eᶜ < 1 → ¬ MOMOn V (measE U E)) ∧
    ((max (ρ E) (ρ Eᶜ) < 1 ∨ min (ρ E) (ρ Eᶜ) = 0) → 1 ≤ ρ E + ρ Eᶜ →
      MOMOn V (measE U E)) := by sorry
end SurelyBetter.CLB
