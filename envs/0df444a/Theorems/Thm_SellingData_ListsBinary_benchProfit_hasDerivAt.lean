-- Prove2me | Theorems.Thm_SellingData_ListsBinary_benchProfit_hasDerivAt
-- name    : SellingData.ListsBinary.benchProfit_hasDerivAt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:46.821352+00:00
-- url     : https://prove2.me/theorems/e6258b8f-845f-4222-a929-8c4bb3e129b3
-- title:
--   Proof of Proposition 1, p. 31 — ∂Π_i/∂α_i = θ_i[φ(ū − c_i) − (1 − φ)(u̲ − c_i) − k′(α_i)]
-- statement:
--   In the binary model of *Selling Data to Marketers*, let $\Pi_i(\alpha)=\theta_i\big[\sigma_h(\alpha)[v_h(\alpha)-c]-k(\alpha)\big]$ be the benchmark profit (4) for a weight $\theta_i$ and a targeting cost $c$. Let $a\in(\underline\alpha,\bar\alpha)$ be an interior informativeness at which the selling cost $k$ is differentiable with derivative $k'(a)$. Then $\Pi_i$ is differentiable at $a$ and
--   $$\frac{\partial\Pi_i}{\partial\alpha}(a)=\theta_i\big[\phi(\bar u-c)-(1-\phi)(\underline u-c)-k'(a)\big].$$
--
--   The marginal value of information is linear in the cost $c$, with slope $\theta_i(1-2\phi)$; this is the input to the comparative statics of Proposition 1.
--
--   **Formalization Note** The derivative is stated as `HasDerivAt` at an interior point, with only the differentiability of $k$ at that point assumed; $\theta_i$ and $c$ are arbitrary reals.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 31, proof of Proposition 1

import Mathlib
import Definitions.Def_SellingData_ListsBinary_Setting

namespace SellingData.ListsBinary

/-- Proof of Proposition 1, p. 31: at an interior informativeness `a` where `k` has derivative
`k'`, `∂Π_i/∂α_i = θ_i[φ(ū - c_i) - (1 - φ)(u̲ - c_i) - k'(α_i)]`. -/
theorem benchProfit_hasDerivAt (M : Model) (θi c a k' : ℝ)
    (ha : a ∈ Set.Ioo M.aLo M.aHi) (hk : HasDerivAt M.k k' a) :
    HasDerivAt (fun α => M.benchProfit θi c α)
      (θi * (M.phi * (M.uHi - c) - (1 - M.phi) * (M.uLo - c) - k')) a := by sorry

end SellingData.ListsBinary
