-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_associated_sum_convex_order
-- name    : QuadraticProbe717.Insertion.associated_sum_convex_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:02.316223+00:00
-- url     : https://prove2.me/theorems/0d61c4de-9140-4d85-9e67-86f58c72b867
-- title:
--   Claim 5.3 — convex comparison with independent marginals
-- statement:
--   Let $X_1,\ldots,X_s$ be measurable, positively associated random variables taking values in $\{0,1\}$. Write $S=\sum_iX_i$. Let $X_i^\perp$ be independent with the same individual laws as the $X_i$, and write $S^\perp=\sum_iX_i^\perp$. For every real convex function $\varphi$ for which the two expectations exist,
--   $$\mathbb E[\varphi(S^\perp)]\le\mathbb E[\varphi(S)].$$
--   There is no positive-mean assumption. The independent comparison is constructed as a product of the actual marginals; putting it on a separate probability space changes neither expectation.
--
--   Differences from the source:
--   - encoding: independent copies with matching marginals, also independent of the original vector → the product of the pushforward marginal laws; reason: only separate expectations occur, so the cross-independence coupling is immaterial
--   - encoding: Bernoulli random variables and expectations that exist → measurable real coordinates taking exactly 0 or 1, with both displayed integrals integrable; reason: the same indicator laws and finite expectations; no positive-mean premise is added
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Claim 5.3 and preceding comparison-law paragraph, p. 9 (PDF p. 9)

import Definitions.Def_QuadraticProbe717_Insertion_association

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem associated_sum_convex_order {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : ℕ) (X : Fin s → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hbits : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hassoc : PositivelyAssociated P X) (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (hleft : Integrable (fun x : Fin s → ℝ => φ (∑ i, x i)) (independentMarginals s P X))
    (hright : Integrable (fun ω => φ (indicatorSum s X ω)) P) :
    (∫ x : Fin s → ℝ, φ (∑ i, x i) ∂independentMarginals s P X) ≤
      ∫ ω, φ (indicatorSum s X ω) ∂P := by sorry

end QuadraticProbe717.Insertion
