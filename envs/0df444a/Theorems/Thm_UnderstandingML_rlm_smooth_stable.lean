-- Prove2me | Theorems.Thm_UnderstandingML_rlm_smooth_stable
-- name    : UnderstandingML.rlm_smooth_stable
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:17:12.09047+00:00
-- url     : https://prove2.me/theorems/b7bb51d8-49ab-44f5-ba85-b87c82e7627f
-- title:
--   Corollary 13.7: for a β-smooth nonnegative loss and λ ≥ 2β/m, RLM satisfies E[ℓ(A(S⁽ⁱ⁾), zᵢ) − ℓ(A(S), zᵢ)] ≤ (48β/(λm)) E[L_S(A(S))], and ≤ 48βC/(λm) if ℓ(0, z) ≤ C
-- statement:
--   **Corollary 13.7.** Assume that the loss function is $\beta$-smooth and nonnegative. Then the RLM rule with the regularizer $\lambda\|w\|^2$, where $\lambda \ge \frac{2\beta}{m}$, satisfies
--   $$\mathbb{E}\big[\ell(A(S^{(i)}), z_i) - \ell(A(S), z_i)\big] \le \frac{48\beta}{\lambda m}\,\mathbb{E}[L_S(A(S))].$$
--   If moreover $\ell(0, z) \le C$ for all $z$, the left-hand side is at most $\frac{48\beta C}{\lambda m}$.
--
--   Formally: the pointwise bound $\ell(A(S^{(i)}), z_i) - \ell(A(S), z_i) \le \frac{24\beta}{\lambda m}(\ell(A(S), z_i) + \ell(A(S^{(i)}), z'))$ of the book's derivation, and the two expectation bounds; the loss is also convex, as throughout §13.3. Measurability: jointly measurable loss and measurable algorithm, with a nonnegative loss bounded at the origin so that all expectations exist (for the RLM rule the minimizer is unique, so measurability of the algorithm is automatic).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §13.3.2 pp. 177-178, Corollary 13.7 with its derivation (13.12)-(13.14) and the remark after it

import Definitions.Def_UnderstandingML_Convex

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Corollary 13.7** (p. 178). Assume that the loss function is `β`-smooth and nonnegative.
Then the RLM rule with the regularizer `λ‖w‖²`, where `λ ≥ 2β/m`, satisfies
`E[ℓ(A(S⁽ⁱ⁾), zᵢ) − ℓ(A(S), zᵢ)] ≤ (48β/(λm)) E[L_S(A(S))]`; and if `ℓ(0, z) ≤ C` for all `z` then
the left-hand side is at most `48βC/(λm)`. The first clause is the book's pointwise bound
`ℓ(A(S⁽ⁱ⁾), zᵢ) − ℓ(A(S), zᵢ) ≤ (24β/(λm))(ℓ(A(S), zᵢ) + ℓ(A(S⁽ⁱ⁾), z'))`. Convexity of the loss
(as in §13.3) and measurability as in Corollary 13.6. -/
theorem rlm_smooth_stable {d : ℕ} {Z : Type*} [MeasurableSpace Z] (loss : Vec d → Z → ℝ)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z)) (hnonneg : ∀ w z, 0 ≤ loss w z)
    {β : ℝ} (hβ : 0 ≤ β) (hsmooth : IsSmoothLoss β loss) {lam : ℝ} (hlam : 0 < lam)
    (A : Learner Z (Vec d)) (hA : IsRLMLearner loss lam A)
    (hmeas : Measurable (Function.uncurry loss)) {C : ℝ} (hC : ∀ z, loss 0 z ≤ C)
    (hAmeas : ∀ m, Measurable (A m)) (m : ℕ) (hm : 0 < m) (hlm : 2 * β / m ≤ lam) :
    (∀ (S : Fin m → Z) (i : Fin m) (z' : Z),
        loss (A m (Function.update S i z')) (S i) - loss (A m S) (S i) ≤
          24 * β / (lam * m) * (loss (A m S) (S i) + loss (A m (Function.update S i z')) z')) ∧
    ∀ (D : Measure Z), IsProbabilityMeasure D →
      (∑ i, ∫ p : (Fin m → Z) × Z,
          (loss (A m (Function.update p.1 i p.2)) (p.1 i) - loss (A m p.1) (p.1 i))
            ∂((iidLaw D m).prod D)) / m ≤
        48 * β / (lam * m) * ∫ S, empRisk loss S (A m S) ∂(iidLaw D m) ∧
      (∑ i, ∫ p : (Fin m → Z) × Z,
          (loss (A m (Function.update p.1 i p.2)) (p.1 i) - loss (A m p.1) (p.1 i))
            ∂((iidLaw D m).prod D)) / m ≤ 48 * β * C / (lam * m) := by sorry

end UnderstandingML
