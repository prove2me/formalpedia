-- Prove2me | Theorems.Thm_UnfairML_Coverage_eq_54
-- name    : UnfairML.Coverage.eq_54
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:36.630522+00:00
-- url     : https://prove2.me/theorems/2c92e921-e64e-4981-a6b8-e8720b738492
-- title:
--   Eqs. (53)–(54), p. 44 — the difference of the two closed forms in terms of σ
-- statement:
--   Under the standing assumptions, case (1), and the cost range of p. 23 with $k=\alpha_r\gamma_r+\sigma^2(\alpha_p\gamma_r-\beta_p\gamma_r+\beta_p\gamma_p)$, $\sigma\in[\rho,1)$, the difference of the closed forms (51) and (52) is
--   $$\frac{\gamma_r}{\gamma_r-\gamma_p}\left[2-\left(\frac{k-\alpha_r\gamma_r}{\alpha_p\gamma_r+\beta_p\gamma_p-\beta_p\gamma_r}\right)^{1/2}-\left(\frac{\beta_p\gamma_p}{k-\alpha_r\gamma_r+\beta_p\gamma_r-\alpha_p\gamma_r}\right)^{1/2}\right]=\frac{\gamma_r}{\gamma_r-\gamma_p}\left[2-\sigma-\left(\frac{\beta_p\gamma_p}{\sigma^2\beta_p\gamma_p+(1-\sigma^2)(\beta_p\gamma_r-\alpha_p\gamma_r)}\right)^{1/2}\right].$$
--
--   This expresses $\phi^{ET}_p-\phi^{EO}_p$ through the single cost parameter $\sigma$.
--
--   **Formalization Note** The page prints the prefactor of (54) as $1/(\gamma_r-\gamma_p)$; equation (53) has $\gamma_r/(\gamma_r-\gamma_p)$, and the identity holds only with that factor, which is what is stated (labelled correction).
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), p. 44, proof of Theorem 2, eqs. (53)–(54)

import Mathlib
import Definitions.Def_UnfairML_Coverage_Model

namespace UnfairML.Coverage

/-- Eqs. (53)–(54), p. 44: with `k = αrγr + σ²(αpγr − βpγr + βpγp)`, the difference of the closed
forms (51) and (52) equals `γr/(γr − γp) · [2 − σ − (βpγp/(σ²βpγp + (1 − σ²)(βpγr − αpγr)))^{1/2}]`.
(The page prints the prefactor of (54) as `1/(γr − γp)`; (53) and the identity need `γr/(γr − γp)`.) -/
theorem eq_54 (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k σ : ℝ)
    (hC : CostRange P k σ) :
    P.γr / (P.γr - P.γp) * (1 - Real.sqrt ((k - P.αr * P.γr) / P.Acoef)) -
      P.γr / (P.γr - P.γp) *
        (Real.sqrt (P.βp * P.γp / (k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr)) - 1) =
    P.γr / (P.γr - P.γp) *
      (2 - σ - Real.sqrt (P.βp * P.γp /
        (σ ^ 2 * P.βp * P.γp + (1 - σ ^ 2) * (P.βp * P.γr - P.αp * P.γr)))) := by sorry
end UnfairML.Coverage
