-- Prove2me | Theorems.Thm_RWPI_SqrtLasso_proposition_1
-- name    : RWPI.SqrtLasso.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:08:35.382933+00:00
-- url     : https://prove2.me/theorems/bf770ffb-0bdf-4252-b432-370d8816cc4a
-- title:
--   Proposition 1 — strong duality for the worst-case expected loss over an optimal-transport ball, with the minimum attained
-- statement:
--   Let $(X_1,Y_1),\dots,(X_n,Y_n)\in\mathbb R^d\times\mathbb R$ be training data, $n\ge1$, with empirical distribution $P_n = \frac1n\sum_{i=1}^n\delta_{(X_i,Y_i)}$. Let $c:\mathbb R^{d+1}\times\mathbb R^{d+1}\to[0,\infty]$ be a lower semicontinuous cost with $c(z,z) = 0$ for every $z$, and let $l:\mathbb R^d\times\mathbb R\to[0,\infty)$ be an upper semicontinuous loss. For $\gamma\ge0$ let
--
--   $$
--   \varphi_\gamma(X_i,Y_i) = \sup_{u\in\mathbb R^d,\ v\in\mathbb R}\big\{ l(u,v) - \gamma\, c\big((u,v),(X_i,Y_i)\big)\big\} \qquad (11)
--   $$
--
--   (terms with infinite cost do not contribute). Then for every $\delta>0$
--
--   $$
--   \sup_{P:\ D_c(P,P_n)\le\delta} \mathbb E_P\big[l(X,Y)\big] = \min_{\gamma\ge0}\Big\{ \gamma\delta + \frac1n\sum_{i=1}^n \varphi_\gamma(X_i,Y_i)\Big\},
--   $$
--
--   and the minimum is attained: there is $\gamma^\ast\ge0$ achieving equality, and the left side is at most the bracket for every $\gamma\ge0$.
--
--   The proposition turns the supremum over uncountably many probability measures into a one-dimensional convex minimization, in which $\varphi_\gamma$ is often explicit. The paper quotes it from Blanchet and Murthy (Math. Oper. Res., 2019, Theorem 1). Taking the infimum over the regression parameter on both sides gives the paper's identity (12); in the paper the loss is $l(\cdot;\beta)$, and the statement here holds for each fixed $\beta$.
--
--   **Formalization Note** Two hypotheses are added to the page and recorded: $l\ge0$ (every loss in the paper is nonnegative; the expectation is a lower Lebesgue integral), and $\delta>0$ (assumed in Blanchet–Murthy; at $\delta = 0$ the minimum need not be attained). Both sides take values in $[0,\infty]$; "min" is stated as attainment plus a lower bound. Identity (12) is not stated separately. The data space is $(\text{Fin } d\to\mathbb R)\times\mathbb R$ with the product topology.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 10, Proposition 1 (first identity; quoted from Blanchet & Murthy 2019, Theorem 1)

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_RWPI_SqrtLasso_worstCase
import Definitions.Def_RWPI_SqrtLasso_phi

open MeasureTheory

namespace RWPI.SqrtLasso

/-- Proposition 1 (Blanchet, Kang & Murthy, p. 10; quoted from Blanchet & Murthy, Math. Oper. Res.
2019, Theorem 1), first identity: strong duality for the worst-case expected loss over the
optimal-transport ball `{P : D_c(P, P_n) ≤ δ}` around the empirical distribution `P_n` of the data
`(X_i, Y_i)`, with the minimum over `γ ≥ 0` attained.
The cost `c` is lower semicontinuous, `[0, ∞]`-valued and vanishes on the diagonal; the loss `l` is
upper semicontinuous. Added hypotheses (recorded): `l ≥ 0` (every loss of the paper) and `δ > 0`
(assumed in Blanchet–Murthy; at `δ = 0` the minimum need not be attained). -/
theorem proposition_1 {d n : ℕ} (hn : 0 < n) (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ)
    (c : (Fin d → ℝ) × ℝ → (Fin d → ℝ) × ℝ → ENNReal)
    (hc : LowerSemicontinuous (Function.uncurry c)) (hc0 : ∀ z, c z z = 0)
    (l : (Fin d → ℝ) × ℝ → ℝ) (hl : UpperSemicontinuous l) (hl0 : ∀ z, 0 ≤ l z)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ γ : ℝ, 0 ≤ γ ∧
      worstCase c δ (WassersteinDRO.Regularization.empiricalDistribution
          (fun i : Fin n => (X i, Y i))) l =
        ENNReal.ofReal (γ * δ) + (n : ENNReal)⁻¹ * ∑ i, phi c l γ (X i, Y i) ∧
      ∀ γ' : ℝ, 0 ≤ γ' →
        worstCase c δ (WassersteinDRO.Regularization.empiricalDistribution
            (fun i : Fin n => (X i, Y i))) l ≤
          ENNReal.ofReal (γ' * δ) + (n : ENNReal)⁻¹ * ∑ i, phi c l γ' (X i, Y i) := by sorry

end RWPI.SqrtLasso
