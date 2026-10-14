-- Prove2me | Theorems.Thm_SCInfoDesign_Intersecting_proposition_3
-- name    : SCInfoDesign.Intersecting.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:58.82603+00:00
-- url     : https://prove2.me/theorems/9993078e-bb76-4b75-a2ab-5112959ff78d
-- title:
--   Proposition 3, p. 15 — intersecting supports: full disclosure for ξ ≥ ξ̆, no disclosure on [τ̲_IS(p₀), ξ̆), and Γ*_IS of (7) for ξ < τ̲_IS(p₀)
-- statement:
--   Let the demand supports intersect without being nested, $b_0>b_1>a_0>a_1\ge 0$, let $0<\xi<1$, and let the prior be $p_0\in[0,1]$. Define $\delta_u=b_0-b_1$, $\delta_d=a_0-a_1$, $\delta_{\mathsf{IS}}=b_1-a_0$ and suppose
--   $$
--   \delta_d>2\delta_u\qquad\text{and}\qquad \delta_{\mathsf{IS}}>\max\Big(\delta_d-2\delta_u,\ \frac{\delta_d\delta_u}{\delta_d-2\delta_u}\Big).
--   $$
--   With $\underline\tau_{\mathsf{IS}}(p)=(1-p)(a_0-a_1)/(b_1-a_1)$, the retailer's optimal policy is as follows.
--
--   1. If $\xi\in\big[\frac{\delta_d-2\delta_u}{\delta_d-\delta_u},1\big)$, full disclosure is optimal.
--   2. If $\xi\in\big[\underline\tau_{\mathsf{IS}}(p_0),\frac{\delta_d-2\delta_u}{\delta_d-\delta_u}\big)$, no disclosure is optimal.
--   3. If $\xi\in(0,\underline\tau_{\mathsf{IS}}(p_0))$, the policy $\Gamma^*_{\mathsf{IS}}$ with messages $\{m_0,m_1\}$ and
--   $$
--   \pi^*_{\mathsf{IS}}(m_0\mid\omega=0)=1,\qquad \pi^*_{\mathsf{IS}}(m_0\mid\omega=1)=\frac{\xi(b_1-a_1)}{(a_0-a_1)-\xi(b_1-a_1)}\cdot\frac{p_0}{1-p_0}
--   $$
--   is optimal.
--
--   Here "optimal" means: the policy, together with some best response of the supplier, attains a retailer cost no larger than that of any policy on any finite message space under any best response. The result shows that with overlapping supports the informativeness of the optimal policy is non-monotone in the critical ratio: partial, then none, then full disclosure as $\xi$ rises.
--
--   **Formalization Note** In each case the statement also asserts that the named map is a policy. Full disclosure sends message $i$ in state $i$; no disclosure is the one-message policy. The hypotheses $0\le a_1$ (nonnegative demand) and $0<\xi<1$ are the paper's implicit standing assumptions; $\delta_d,\delta_u,\delta_{\mathsf{IS}}>0$ is the support ordering $b_0>b_1>a_0>a_1$.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 15, Proposition 3, (7)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Intersecting_Setting

namespace SCInfoDesign.Intersecting
theorem proposition_3 (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (h2 : 2 * P.δu < P.δd) (hmax : max (P.δd - 2 * P.δu) (P.δd * P.δu / (P.δd - 2 * P.δu)) < P.δIS)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) :
    (P.ξbreve ≤ P.ξ → P.IsOptimalPolicy p₀ SCInfoDesign.Nested.fullDisclosure) ∧
    (P.τlowIS p₀ ≤ P.ξ → P.ξ < P.ξbreve → P.IsOptimalPolicy p₀ SCInfoDesign.Nested.noDisclosure) ∧
    (P.ξ < P.τlowIS p₀ → P.IsOptimalPolicy p₀ (P.gammaStarIS p₀)) := by sorry
end SCInfoDesign.Intersecting
