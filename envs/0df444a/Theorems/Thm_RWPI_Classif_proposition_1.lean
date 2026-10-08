-- Prove2me | Theorems.Thm_RWPI_Classif_proposition_1
-- name    : RWPI.Classif.proposition_1
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-05T17:52:20.894788+00:00
-- url     : https://prove2.me/theorems/3ea5c013-58bf-4610-a0c3-c4dd1b81dc34
-- title:
--   Proposition 1 — strong duality for the worst-case expected loss over an optimal-transport ball
-- statement:
--   Let $Z = \mathbb R^d \times \mathbb R$ and let $c : Z \times Z \to [0,\infty]$ be a lower semicontinuous cost function with $c(z,z) = 0$ for every $z \in Z$. Let $l : Z \to [0,\infty)$ be an upper semicontinuous nonnegative loss. Let $(X_1,Y_1),\dots,(X_n,Y_n) \in Z$ with $n \ge 1$, let $P_n$ be their empirical distribution, and let $\delta > 0$. For $\gamma \ge 0$ put
--
--   $$\varphi_\gamma(X_i,Y_i) = \sup_{u \in \mathbb R^d,\ v \in \mathbb R}\big\{ l(u,v) - \gamma\, c\big((u,v),(X_i,Y_i)\big) \big\}.$$
--
--   Then
--
--   $$\sup_{P:\ D_c(P,P_n)\le\delta} \mathbb E_P\big[l(X,Y)\big] = \min_{\gamma \ge 0}\Big\{ \gamma\delta + \frac1n \sum_{i=1}^n \varphi_\gamma(X_i,Y_i) \Big\},$$
--
--   and the minimum on the right is attained: there is $\gamma^* \ge 0$ at which the right-hand expression equals the left-hand side, and the left-hand side is at most the right-hand expression for every $\gamma \ge 0$. Both sides take values in $[0,\infty]$.
--
--   This strong duality turns the supremum over infinitely many distributions into a one-dimensional minimization, and is the first step in recovering regularized estimators as distributionally robust ones. The paper quotes it from Blanchet & Murthy (Math. Oper. Res. 2019, Theorem 1).
--
--   **Formalization Note** The loss is a fixed function $l$ (the parameter $\beta$ of the paper plays no role in the identity; the paper's consequence (12) follows by taking the infimum over $\beta$ on both sides). Two restrictions relative to the page are recorded: the loss is nonnegative, so expectations are lower Lebesgue integrals in $[0,\infty]$, and the radius is strictly positive, as in Blanchet & Murthy's theorem (at $\delta = 0$ the minimum need not be attained). $\varphi_\gamma$ is computed in $[0,\infty]$ with the convention $\infty\cdot 0 = 0$.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 10, Proposition 1 (from Blanchet & Murthy 2019, Theorem 1)

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_RWPI_SqrtLasso_worstCase
import Definitions.Def_RWPI_Classif_phi

open MeasureTheory
open scoped ENNReal

namespace RWPI.Classif

/-- Proposition 1, p. 10 (from Blanchet & Murthy, Math. Oper. Res. 2019, Theorem 1): for a
lower semicontinuous cost `c : ℝ^{d+1} × ℝ^{d+1} → [0, ∞]` vanishing on the diagonal, an upper
semicontinuous nonnegative loss `l` and a radius `δ > 0`, the worst-case expected loss over
`{P : D_c(P, P_n) ≤ δ}` equals `min_{γ ≥ 0} { γδ + (1/n) Σᵢ φ_γ(Xᵢ, Yᵢ) }`, the minimum being
attained. -/
theorem proposition_1 {d n : ℕ} (hn : 0 < n) (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ)
    (c : (Fin d → ℝ) × ℝ → (Fin d → ℝ) × ℝ → ℝ≥0∞)
    (hc : LowerSemicontinuous (Function.uncurry c)) (hc0 : ∀ z, c z z = 0)
    (l : (Fin d → ℝ) × ℝ → ℝ) (hl : UpperSemicontinuous l) (hl0 : ∀ z, 0 ≤ l z)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ γ : ℝ, 0 ≤ γ ∧
      RWPI.SqrtLasso.worstCase c δ
          (WassersteinDRO.Regularization.empiricalDistribution (fun i => (X i, Y i))) l =
        ENNReal.ofReal (γ * δ) + (n : ℝ≥0∞)⁻¹ * ∑ i, phi c l γ (X i, Y i) ∧
      ∀ γ' : ℝ, 0 ≤ γ' →
        RWPI.SqrtLasso.worstCase c δ
            (WassersteinDRO.Regularization.empiricalDistribution (fun i => (X i, Y i))) l ≤
          ENNReal.ofReal (γ' * δ) + (n : ℝ≥0∞)⁻¹ * ∑ i, phi c l γ' (X i, Y i) := by sorry

end RWPI.Classif
