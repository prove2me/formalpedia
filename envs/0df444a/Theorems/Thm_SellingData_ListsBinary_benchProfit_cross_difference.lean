-- Prove2me | Theorems.Thm_SellingData_ListsBinary_benchProfit_cross_difference
-- name    : SellingData.ListsBinary.benchProfit_cross_difference
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:54.942632+00:00
-- url     : https://prove2.me/theorems/d003f8f7-1705-4900-8fa9-327322ee8dcc
-- title:
--   Proof of Proposition 1, p. 31 — cross derivative ∂²Π_i/∂α_i∂c_i = θ_i(1 − 2φ), integrated form
-- statement:
--   In the binary model of *Selling Data to Marketers*, let $\Pi_i(\alpha,c)=\theta_i\big[\sigma_h(\alpha)[v_h(\alpha)-c]-k(\alpha)\big]$ be the benchmark profit (4) as a function of the informativeness $\alpha$ and the targeting cost $c$. For all real $\alpha,\alpha',c,c'$,
--   $$\big[\Pi_i(\alpha',c')-\Pi_i(\alpha,c')\big]-\big[\Pi_i(\alpha',c)-\Pi_i(\alpha,c)\big]=\theta_i(1-2\phi)(\alpha'-\alpha)(c'-c).$$
--
--   This is the cross derivative $\partial^2\Pi_i/\partial\alpha_i\partial c_i=\theta_i(1-2\phi)$ of the proof of Proposition 1, in the integrated form that a lattice-theoretic comparative-statics argument uses: $\Pi_i$ has strictly increasing differences in $(\alpha,c)$ when $\phi<1/2$ and strictly decreasing differences when $\phi>1/2$.
--
--   **Formalization Note** The paper writes a second derivative; the mission states the equivalent mixed second difference, which needs no differentiability of $k$.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 31, proof of Proposition 1

import Mathlib
import Definitions.Def_SellingData_ListsBinary_Setting

namespace SellingData.ListsBinary

/-- Proof of Proposition 1, p. 31: the cross derivative `∂²Π_i/∂α_i∂c_i = θ_i(1 - 2φ)`, in
integrated (mixed-difference) form. -/
theorem benchProfit_cross_difference (M : Model) (θi c c' α α' : ℝ) :
    (M.benchProfit θi c' α' - M.benchProfit θi c' α) -
        (M.benchProfit θi c α' - M.benchProfit θi c α) =
      θi * (1 - 2 * M.phi) * (α' - α) * (c' - c) := by sorry

end SellingData.ListsBinary
