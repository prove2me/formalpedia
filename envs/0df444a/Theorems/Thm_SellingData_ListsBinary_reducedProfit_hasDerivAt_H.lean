-- Prove2me | Theorems.Thm_SellingData_ListsBinary_reducedProfit_hasDerivAt_H
-- name    : SellingData.ListsBinary.reducedProfit_hasDerivAt_H
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:50.331369+00:00
-- url     : https://prove2.me/theorems/c6cd2c67-5b26-42fe-8082-08d0b1884584
-- title:
--   Proof of Proposition 2, p. 31 — ∂Π/∂α_H of (7) = θ[φ(ū − c_H) − (1 − φ)(u̲ − c_H) − k′(α_H)] + (1 − θ)(1 − 2φ)(c_H − c_L)
-- statement:
--   In the screening problem of *Selling Data to Marketers* for marketing lists, let $\Pi^{(7)}(\alpha_H,\alpha_L)$ be the objective of (7). Fix $\alpha_L$ and let $a\in(\underline\alpha,\bar\alpha)$ be a point at which the selling cost $k$ is differentiable with derivative $k'(a)$. Then $\alpha_H\mapsto\Pi^{(7)}(\alpha_H,\alpha_L)$ is differentiable at $a$ and
--   $$\frac{\partial\Pi^{(7)}}{\partial\alpha_H}(a)=\theta\big[\phi(\bar u-c_H)-(1-\phi)(\underline u-c_H)-k'(a)\big]+(1-\theta)(1-2\phi)(c_H-c_L).$$
--
--   Compared with the benchmark derivative for the high-cost type, the extra term $(1-\theta)(1-2\phi)(c_H-c_L)$ is the marginal effect of $\alpha_H$ on the information rent $\sigma_h(\alpha_H)(c_H-c_L)$ conceded to low-cost marketers; its sign is that of $1-2\phi$.
--
--   **Formalization Note** Stated as `HasDerivAt` at an interior point, with only the differentiability of $k$ at that point assumed.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 31, proof of Proposition 2

import Mathlib
import Definitions.Def_SellingData_ListsBinary_Setting

namespace SellingData.ListsBinary

/-- Proof of Proposition 2, p. 31: the derivative of the objective (7) in `α_H`,
`∂Π/∂α_H = θ[φ(ū - c_H) - (1 - φ)(u̲ - c_H) - k'(α_H)] + (1 - θ)(1 - 2φ)(c_H - c_L)`. -/
theorem reducedProfit_hasDerivAt_H (S : Screening) (αL a k' : ℝ)
    (ha : a ∈ Set.Ioo S.aLo S.aHi) (hk : HasDerivAt S.k k' a) :
    HasDerivAt (fun α => S.reducedProfit α αL)
      (S.θ * (S.phi * (S.uHi - S.cH) - (1 - S.phi) * (S.uLo - S.cH) - k') +
        (1 - S.θ) * (1 - 2 * S.phi) * (S.cH - S.cL)) a := by sorry

end SellingData.ListsBinary
