-- Prove2me | Theorems.Thm_RUCVaR_MinFormula_argmin_characterization
-- name    : RUCVaR.MinFormula.argmin_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:46.894687+00:00
-- url     : https://prove2.me/theorems/26a9b742-0b25-42f6-a55e-3bc4017e7d4e
-- title:
--   Proof of Theorem 10, p. 16 — bounded level sets; argmin F_β(x, ·) = {α | Ψ(x, α⁻) ≤ β ≤ Ψ(x, α)}, a nonempty closed bounded interval
-- statement:
--   Let $P$ be a probability measure on $\mathbb R^m$, let the loss $y\mapsto f(x,y)$ be measurable and integrable, and let $0<\beta<1$. Then:
--
--   1. every level set $\{\alpha \mid F_\beta(x,\alpha)\le c\}$ is bounded;
--   2. the set of minimizers of $F_\beta(x,\cdot)$ over $\mathbb R$ is
--   $$
--   \operatorname{argmin}_\alpha F_\beta(x,\alpha)=\{\alpha\in\mathbb R \mid \Psi(x,\alpha^-)\le\beta\le\Psi(x,\alpha)\};
--   $$
--   3. this set is nonempty, closed, bounded, and an interval.
--
--   This is the step of the proof of Theorem 10 in which the minimum in (28) is shown to be attained and its argmin is identified through the one-sided derivatives.
--
--   **Formalization Note** The argmin is the set of global minimizers ($\alpha$ with $F_\beta(x,\alpha)\le F_\beta(x,\alpha')$ for all $\alpha'$), not the set where $F_\beta$ equals an infimum. "Interval" is order-connectedness. Only the single loss $f(x,\cdot)$ is assumed measurable and integrable; the other standing assumptions are dropped.
-- source:
--   Rockafellar & Uryasev, Conditional value-at-risk for general loss distributions, Research Report #2001-5, Univ. of Florida, April 4, 2001, p. 16, proof of Theorem 10

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RUCVaR_MinFormula_Setting
open MeasureTheory Filter Topology

namespace RUCVaR.MinFormula

/-- Proof of Theorem 10, p. 16: the level sets of `F_β(x, ·)` are bounded, and the argmin is the
nonempty, closed, bounded interval `{α | Ψ(x, α⁻) ≤ β ≤ Ψ(x, α)}`. -/
theorem argmin_characterization {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (x : Fin n → ℝ) (hmeas : Measurable (f x))
    (hint : Integrable (f x) P) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ c : ℝ, Bornology.IsBounded {α : ℝ | Fbeta P f β x α ≤ c}) ∧
    {α : ℝ | IsMinOn (Fbeta P f β x) Set.univ α} =
      {α : ℝ | PsiLeft P f x α ≤ β ∧ β ≤ Psi P f x α} ∧
    ({α : ℝ | PsiLeft P f x α ≤ β ∧ β ≤ Psi P f x α}.Nonempty ∧
      IsClosed {α : ℝ | PsiLeft P f x α ≤ β ∧ β ≤ Psi P f x α} ∧
      Bornology.IsBounded {α : ℝ | PsiLeft P f x α ≤ β ∧ β ≤ Psi P f x α} ∧
      Set.OrdConnected {α : ℝ | PsiLeft P f x α ≤ β ∧ β ≤ Psi P f x α}) := by sorry

end RUCVaR.MinFormula
