-- Prove2me | Theorems.Thm_SellingData_AppendsBinary_deriv_alphaL
-- name    : SellingData.AppendsBinary.deriv_alphaL
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:40.55214+00:00
-- url     : https://prove2.me/theorems/ce6c4ab5-d6a7-4f2e-b961-c0c01c01f8a8
-- title:
--   Proof of Proposition 3, p. 32 — ∂Π/∂α_L of the benchmark and of (8)
-- statement:
--   In the data-append model, let $\alpha_H$ be arbitrary and let $\alpha_L\in[\underline\alpha,\bar\alpha]$ be a point at which the selling cost $k$ has derivative $k'(\alpha_L)$. Then the low-cost benchmark profit $\Pi_L(\alpha)=(1-\theta)[\sigma_h(\alpha)[v_h(\alpha)-c_L]-k(\alpha)]$ of (4) has derivative
--   $$\frac{\partial\Pi_L}{\partial\alpha_L}=(1-\theta)\big[\varphi(\bar u-c_L)-(1-\varphi)(\underline u-c_L)-k'(\alpha_L)\big]$$
--   at $\alpha_L$, and the objective $\Pi$ of (8), as a function of $\alpha_L$, has derivative
--   $$\frac{\partial\Pi}{\partial\alpha_L}=(1-\theta)\big[\varphi(\bar u-c_L)-(1-\varphi)(\underline u-c_L)-k'(\alpha_L)\big]+\theta(1-2\varphi)(c_L-c_H)$$
--   at $\alpha_L$.
--
--   The two derivatives differ by the constant $\theta(1-2\varphi)(c_L-c_H)$, which is negative when $\varphi<1/2$ and positive when $\varphi>1/2$; this comparison is what drives the direction of the distortion in Proposition 3.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 32, proof of Proposition 3, display for ∂Π/∂α_L

import Mathlib
import Definitions.Def_SellingData_AppendsBinary_Setting

namespace SellingData.AppendsBinary

open Model

/-- Proof of Proposition 3, p. 32: the derivative in `α_L` of the benchmark profit (4) of the
low-cost type is `(1 − θ)[φ(ū − c_L) − (1 − φ)(u̲ − c_L) − k′(α_L)]`, and that of the objective (8)
is `(1 − θ)[φ(ū − c_L) − (1 − φ)(u̲ − c_L) − k′(α_L)] + θ(1 − 2φ)(c_L − c_H)`. -/
theorem deriv_alphaL (M : Model) (αH a k' : ℝ) (ha : a ∈ Set.Icc M.aLo M.aHi)
    (hk : HasDerivAt M.k k' a) :
    HasDerivAt (fun α => M.benchProfit SellingData.ListsBinary.CostType.L α)
        ((1 - M.θ) * (M.φ * (M.uHi - M.cL) - (1 - M.φ) * (M.uLo - M.cL) - k')) a ∧
      HasDerivAt (fun α => M.reducedProfit αH α)
        ((1 - M.θ) * (M.φ * (M.uHi - M.cL) - (1 - M.φ) * (M.uLo - M.cL) - k')
          + M.θ * (1 - 2 * M.φ) * (M.cL - M.cH)) a := by sorry

end SellingData.AppendsBinary
