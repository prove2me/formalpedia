-- Prove2me | Theorems.Thm_RiskControl_Optimal_expSize_le_of_setdiff
-- name    : RiskControl.Optimal.expSize_le_of_setdiff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:38:30.517001+00:00
-- url     : https://prove2.me/theorems/956119cb-c385-4e7f-bfc8-afc80cd8f17b
-- title:
--   Proof of Theorem 8, p. 27, display 8 — E|A(X)∖B(X)| ≤ E|B(X)∖A(X)| ⟹ E|A(X)| ≤ E|B(X)|
-- statement:
--   Let $P$ be a measure on $\mathcal X \times \mathcal Y$ with marginal $P_X$ on $\mathcal X$, let $\mu$ be a finite measure on $\mathcal Z$, and let $\mathcal A, \mathcal B : \mathcal X \to 2^{\mathcal Z}$ be set-valued predictors with measurable graphs. Write $|\cdot|$ for $\mu$ and $X \sim P_X$. If
--   $$\mathbb E\big[|\mathcal A(X) \setminus \mathcal B(X)|\big] \le \mathbb E\big[|\mathcal B(X) \setminus \mathcal A(X)|\big],$$
--   then
--   $$\mathbb E\big[|\mathcal A(X)|\big] \le \mathbb E\big[|\mathcal B(X)|\big].$$
--
--   This is the last step of the proof of Theorem 8, with $\mathcal A = \mathcal T_\lambda$ and $\mathcal B = \mathcal T'$: adding the common part $\mathbb E|\mathcal A(X) \cap \mathcal B(X)|$ to both sides turns the comparison of the set differences into a comparison of expected sizes.
--
--   **Formalization Note** The step is stated for arbitrary predictors with measurable graphs; integrals are lower Lebesgue integrals in $[0, \infty]$.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, Proof of Theorem 8, p. 27, seventh and eighth displays

import Mathlib
import Definitions.Def_RiskControl_Optimal_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RiskControl.Optimal

/-- Proof of Theorem 8, arXiv:2101.02703v3, p. 27, display 8: for set-valued predictors
`A B : 𝒳 → 2^𝒵` with measurable graphs, `𝔼[|A(X) ∖ B(X)|] ≤ 𝔼[|B(X) ∖ A(X)|]` implies
`𝔼[|A(X)|] ≤ 𝔼[|B(X)|]`, sizes measured by the finite measure `μ` and `X ~ P.fst`
(on the page, `A = 𝒯_λ` and `B = 𝒯′`). -/
theorem expSize_le_of_setdiff {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    [MeasurableSpace 𝒵]
    (P : Measure (𝒳 × 𝒴)) (μ : Measure 𝒵) [IsFiniteMeasure μ]
    (A B : 𝒳 → Set 𝒵) (hA : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ A q.1})
    (hB : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ B q.1})
    (h : ∫⁻ x, μ (A x \ B x) ∂P.fst ≤ ∫⁻ x, μ (B x \ A x) ∂P.fst) :
    expSize P μ A ≤ expSize P μ B := by sorry

end RiskControl.Optimal
