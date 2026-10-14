-- Prove2me | Theorems.Thm_SellingData_ListsRotation_payoff_integration_by_parts
-- name    : SellingData.ListsRotation.payoff_integration_by_parts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:33.286822+00:00
-- url     : https://prove2.me/theorems/6f41cab9-d921-4654-9ec9-d268ab0f7fed
-- title:
--   Proof of Proposition 4, p. 32 — integration by parts: $\int_c^{\bar v}(v-c)\,dH(v,\alpha)=\int_c^{\bar v}[1-H(v,\alpha)]\,dv$
-- statement:
--   In the rotation-order model, fix an informativeness $\alpha\in(0,1)$ and a cost $c$ in the support $[\underline v,\bar v]$ of the posterior mean. Then the marketer's expected surplus from targeting can be rewritten by integrating by parts:
--   $$\int_c^{\bar v}(v-c)\,dH(v,\alpha)=\int_c^{\bar v}\big[1-H(v,\alpha)\big]\,dv .$$
--   Consequently the benchmark problem (12) becomes
--   $$\max_{\alpha_i\in[\underline\alpha,\bar\alpha]}\Pi_i=\theta_i\Big[\int_{c_i}^{\bar v}[1-H(v,\alpha_i)]\,dv-k(\alpha_i)\Big].$$
--
--   This identity expresses every payoff of the model through the distribution function $H$, whose dependence on $\alpha$ is controlled by the rotation order (9); it is the first step of the proofs of Propositions 4 and 5.
--
--   **Formalization Note** $dH(v,\alpha)$ is $h(v,\alpha)\,dv$ with the density $h$ of the model.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 32, proof of Proposition 4, first display

import Mathlib
import Definitions.Def_SellingData_ListsRotation_Setting

namespace SellingData.ListsRotation

/-- Proof of Proposition 4, p. 32: integrating by parts,
`∫_c^{v̄} (v - c) dH(v, α) = ∫_c^{v̄} [1 - H(v, α)] dv`, so (12) reads
`Π_i = θ_i [∫_{c_i}^{v̄} [1 - H(v, α_i)] dv - k(α_i)]`. -/
theorem payoff_integration_by_parts (M : Model) :
    ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ c ∈ Set.Icc M.vLo M.vHi,
      M.payoff α c = ∫ v in c..M.vHi, (1 - M.H v α) := by sorry

end SellingData.ListsRotation
