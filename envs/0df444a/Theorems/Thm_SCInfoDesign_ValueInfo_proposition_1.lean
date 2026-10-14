-- Prove2me | Theorems.Thm_SCInfoDesign_ValueInfo_proposition_1
-- name    : SCInfoDesign.ValueInfo.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:34.793844+00:00
-- url     : https://prove2.me/theorems/82c75c42-65d3-444c-acd7-d3841802c964
-- title:
--   Proposition 1, p. 8 — the supplier's optimal quantity Q*_p is unique and given by (4)
-- statement:
--   Let the demand supports be nested, $0\le a_0\le a_1<b_1\le b_0$ with $a_0<b_0$, let $\xi\in(0,1)$ be the critical ratio and $p\in[0,1]$ the supplier's belief that $\omega=0$. Write $\underline\tau(p)=p(a_1-a_0)/(b_0-a_0)$ and $\bar\tau(p)=1-p(b_0-b_1)/(b_0-a_0)$. Then the supplier's problem (2) has exactly one optimal quantity $Q^*_p$, namely
--   $$Q^*_p=\begin{cases} b_0-\dfrac{(b_0-a_0)(1-\xi)}{p} & \xi\in[\bar\tau(p),1),\\[2mm] \dfrac{b_1(\xi-\underline\tau(p))+a_1(\bar\tau(p)-\xi)}{\bar\tau(p)-\underline\tau(p)} & \xi\in[\underline\tau(p),\bar\tau(p)],\\[2mm] \dfrac{\xi(b_0-a_0)}{p}+a_0 & \xi\in(0,\underline\tau(p)].\end{cases}$$
--   In each case, a quantity $Q$ is optimal for (2) if and only if it equals the displayed value.
--
--   This is the newsvendor quantile of the two-point mixture of uniform laws; it makes the retailer's cost $K$ an explicit function of the belief.
--
--   **Formalization Note** Optimality is the argmin of (2) over $Q\ge 0$ (normalized cost, see the Setting). The nonnegativity $a_0,a_1\ge0$ and the strict ranges $a_0<b_0$, $a_1<b_1$, $0<\xi<1$ are the paper's implicit standing assumptions, made explicit. The three cases are stated as three implications; their closed intervals overlap at the thresholds, where the formulas agree.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 8, Proposition 1, (4)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_ValueInfo_Setting

namespace SCInfoDesign.ValueInfo

/-- Proposition 1 (p. 8): for nested supports, every belief `p ∈ [0, 1]` and every critical
ratio `ξ ∈ (0, 1)`, the supplier's optimal quantity is unique and given by (4). -/
theorem proposition_1
    (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (τup P p ≤ ξ → ∀ Q : ℝ,
        IsOptimalQuantity P ξ p Q ↔ Q = P.b₀ - (P.b₀ - P.a₀) * (1 - ξ) / p) ∧
    (τlow P p ≤ ξ → ξ ≤ τup P p → ∀ Q : ℝ,
        IsOptimalQuantity P ξ p Q ↔
          Q = (P.b₁ * (ξ - τlow P p) + P.a₁ * (τup P p - ξ)) / (τup P p - τlow P p)) ∧
    (ξ ≤ τlow P p → ∀ Q : ℝ,
        IsOptimalQuantity P ξ p Q ↔ Q = ξ * (P.b₀ - P.a₀) / p + P.a₀) := by sorry

end SCInfoDesign.ValueInfo
