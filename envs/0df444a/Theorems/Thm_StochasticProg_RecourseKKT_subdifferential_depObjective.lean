-- Prove2me | Theorems.Thm_StochasticProg_RecourseKKT_subdifferential_depObjective
-- name    : StochasticProg.RecourseKKT.subdifferential_depObjective
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:52:10.202232+00:00
-- url     : https://prove2.me/theorems/cfcef54f-6a16-4c6d-89fe-24ef40e7db95
-- title:
--   Subdifferential of the objective: $\partial(c^{\mathsf T}x+\mathcal Q(x))=c+\partial\mathcal Q(x)$
-- statement:
--   For every point $x^* \in \mathbb R^{n_1}$,
--
--   $$
--   \partial\big(c^{\mathsf T} x^* + \mathcal Q(x^*)\big) = c + \partial \mathcal Q(x^*),
--   $$
--
--   that is, the subgradients of the objective $x \mapsto c^{\mathsf T}x + \mathcal Q(x)$ of (1.2) at $x^*$ are exactly the vectors $c + \zeta$ with $\zeta$ a subgradient of $\mathcal Q$ at $x^*$.
--
--   This lets the proof of Theorem 9 move between a subgradient of the objective and the condition $-c + A^{\mathsf T}\lambda^* + \mu^* \in \partial \mathcal Q(x^*)$ of (1.12).
--
--   **Formalization Note** Both sides are empty when $\mathcal Q(x^*) = \pm\infty$.
--
--   Differences from the source:
--   - generalization: at the point x* of Theorem 9 (under its hypotheses) → at every x*, with no hypothesis; reason: the identity holds everywhere; it specializes to the book's x*
--   - encoding: ∂f(x) = {η | f(w) ≥ f(x) + ηᵀ(w − x) ∀w} → subdifferential with f(x) required real (empty where f(x) = ±∞); reason: the convex-analysis convention for extended-valued functions; at points where 𝒬 is finite it is the book's set
--   - encoding: 𝒬(x) = E_ξ Q(x, ξ) with +∞ + (−∞) = +∞ and 0·∞ = 0 → EReal value: +∞ if ∫⁻ Q⁺ = ∞, else ∫⁻ Q⁺ − ∫⁻ Q⁻; reason: the book's convention written out; same instances
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1e, proof of Theorem 9, printed p. 116 (PDF p. 141)

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_RecourseData
import Definitions.Def_StochasticProg_RecourseKKT_expectedRecourse
import Definitions.Def_StochasticProg_RecourseKKT_depObjective
import Definitions.Def_StochasticProg_RecourseKKT_subdifferential
open MeasureTheory

namespace StochasticProg.RecourseKKT

/-- **Subdifferential of the objective of (1.2) (proof of Theorem 9).**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1e, proof of Theorem 9, printed p. 116 (PDF p. 141):
"∂(cᵀx* + 𝒬(x*)) = c + ∂𝒬(x*)".

For every point `x*`, the subdifferential of `x ↦ cᵀx + 𝒬(x)` at `x*` is the translate by `c` of
the subdifferential of `𝒬` at `x*`.

**Formalization Note.** `subdifferential` is empty where the function is infinite, so both sides
are empty when `𝒬(x*) = ±∞`; no hypothesis on `x*` is needed. -/
theorem subdifferential_depObjective {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (pb : RecourseData Ω n1 m1 n2 m2) (xs : Fin n1 → ℝ) :
    subdifferential (depObjective P pb) xs =
      (fun ζ => pb.c + ζ) '' subdifferential (expectedRecourse P pb) xs := by sorry

end StochasticProg.RecourseKKT
