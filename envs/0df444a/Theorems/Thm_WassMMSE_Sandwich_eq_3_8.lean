-- Prove2me | Theorems.Thm_WassMMSE_Sandwich_eq_3_8
-- name    : WassMMSE.Sandwich.eq_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:38.861992+00:00
-- url     : https://prove2.me/theorems/69b8f85d-9014-4554-b5f7-93012255b4a6
-- title:
--   (3.8), proof of Theorem 3.5, p. 15 — for Σ̂_w ≻ 0, the value of (3.3) as a sup–inf over Σ_x, Σ_w ⪰ λ_min(Σ̂)I and A
-- statement:
--   Let the nominal distribution be normal of the form (3.2) with $\widehat\Sigma_x\succeq0$ and $\widehat\Sigma_w\succ0$, let $H\in\mathbb R^{m\times n}$ and $\rho_x,\rho_w\ge0$. Then
--   $$\sup_{\mathbb Q\in\mathbb B_{\mathcal N}(\widehat{\mathbb P})}\inf_{\psi\in\mathcal F}\mathcal R(\psi,\mathbb Q)=\left\{\begin{aligned}\sup_{\Sigma_x,\Sigma_w}\ &\inf_{A,\,K=I_n-AH}\ \langle K^\top K,\Sigma_x\rangle+\langle A^\top A,\Sigma_w\rangle\\ \text{s.t. }&\operatorname{Tr}\big[\Sigma_x+\widehat\Sigma_x-2(\widehat\Sigma_x^{1/2}\Sigma_x\widehat\Sigma_x^{1/2})^{1/2}\big]\le\rho_x^2\\ &\operatorname{Tr}\big[\Sigma_w+\widehat\Sigma_w-2(\widehat\Sigma_w^{1/2}\Sigma_w\widehat\Sigma_w^{1/2})^{1/2}\big]\le\rho_w^2\\ &\Sigma_x\succeq\lambda_{\min}(\widehat\Sigma_x)I_n,\ \Sigma_w\succeq\lambda_{\min}(\widehat\Sigma_w)I_m.\end{aligned}\right.\tag{3.8}$$
--   Here $\Sigma_x$ and $\Sigma_w$ range over symmetric matrices satisfying the constraints and $A$ over $\mathbb R^{n\times m}$.
--
--   Display (3.8) is the form of the dual problem over normal priors that the proof of the sandwich theorem matches against the reformulation of the Gelbrich MMSE problem.
--
--   **Formalization Note** The left side, in $[0,\infty]$, is coerced to `EReal`; the inner infimum and the outer supremum are `EReal`. The hypothesis $\widehat\Sigma_w\succ0$ is the page's own ("If $\widehat\Sigma_w\succ0$", p. 14, in the sentence that leads to (3.8)). The constraint $\Sigma\succeq\lambda_{\min}(\widehat\Sigma)I$ includes symmetry of $\Sigma$ and, since $\lambda_{\min}(\widehat\Sigma)\ge0$, implies $\Sigma\succeq0$.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 15, (3.8), proof of Theorem 3.5 (hypothesis Σ̂_w ≻ 0 from p. 14)

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_psdSqrt
import Definitions.Def_WassMMSE_Sandwich_Setting
import Definitions.Def_WassMMSE_Sandwich_Programs

open MeasureTheory ProbabilityTheory Matrix WassersteinDRO.Gelbrich

namespace WassMMSE.Sandwich

/-- (3.8), proof of Theorem 3.5 (arXiv:1911.03539v2, p. 15), under "If `Σ̂_w ≻ 0`" (p. 14). For a
normal nominal distribution of the form (3.2) with `Σ̂_w ≻ 0`, the optimal value of (3.3) equals
`sup_{Σ_x, Σ_w} inf_{A, K = I_n − AH} ⟨KᵀK, Σ_x⟩ + ⟨AᵀA, Σ_w⟩` subject to the two Gelbrich trace
constraints and `Σ_x ⪰ λ_min(Σ̂_x) I_n`, `Σ_w ⪰ λ_min(Σ̂_w) I_m`. -/
theorem eq_3_8 {n m : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) (ρx ρw : ℝ) (hρx : 0 ≤ ρx)
    (hρw : 0 ≤ ρw) (μx : E n) (Shx : Matrix (Fin n) (Fin n) ℝ) (hShx : Shx.PosSemidef)
    (μw : E m) (Shw : Matrix (Fin m) (Fin m) ℝ) (hShw : Shw.PosDef) :
    ((normalMaximin H ρx ρw μx Shx μw Shw : ENNReal) : EReal) =
      ⨆ (Sx : Matrix (Fin n) (Fin n) ℝ) (Sw : Matrix (Fin m) (Fin m) ℝ)
        (_ : (Sx + Shx - (2 : ℝ) • psdSqrt (psdSqrt Shx * Sx * psdSqrt Shx)).trace ≤ ρx ^ 2 ∧
          (Sw + Shw - (2 : ℝ) • psdSqrt (psdSqrt Shw * Sw * psdSqrt Shw)).trace ≤ ρw ^ 2 ∧
          (Sx - lamMin Shx • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (Sw - lamMin Shw • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef),
        ⨅ (A : Matrix (Fin n) (Fin m) ℝ),
          ((frob ((1 - A * H)ᵀ * (1 - A * H)) Sx + frob (Aᵀ * A) Sw : ℝ) : EReal) := by sorry

end WassMMSE.Sandwich
