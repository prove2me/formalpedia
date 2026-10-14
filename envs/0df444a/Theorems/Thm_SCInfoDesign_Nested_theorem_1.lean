-- Prove2me | Theorems.Thm_SCInfoDesign_Nested_theorem_1
-- name    : SCInfoDesign.Nested.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:10.949443+00:00
-- url     : https://prove2.me/theorems/a73739a0-d737-4c7a-91bb-026cc24443ed
-- title:
--   Theorem 1, p. 9 — full disclosure for ξ ≥ ξ_h, no disclosure on [τ̲(p₀), ξ_h], and Γ* of (5) for ξ ≤ τ̲(p₀)
-- statement:
--   A retailer knows the state $\omega\in\{0,1\}$ (prior $p_0=\mathbb P(\omega=0)\in[0,1]$) of her demand $D_\omega$, where $D_0\sim U[a_0,b_0]$ and $D_1\sim U[a_1,b_1]$ with nested supports $0\le a_0\le a_1<b_1\le b_0$, $a_0<b_0$. She commits to a disclosure policy; the supplier, with critical ratio $\xi\in(0,1)$, updates his belief by Bayes' rule and solves the newsvendor problem (2); the retailer pays the expected shortage. Let
--   $$\xi_h=\frac{a_1-a_0}{b_0-a_0-b_1+a_1},\qquad \underline\tau(p_0)=\frac{p_0(a_1-a_0)}{b_0-a_0}.$$
--   Then the retailer's optimal policy, over all policies on finite message spaces and all supplier best responses, is as follows:
--
--   1. if $\xi\in[\xi_h,1)$, full disclosure is optimal;
--   2. if $\xi\in[\underline\tau(p_0),\xi_h]$, no disclosure is optimal;
--   3. if $\xi\in(0,\underline\tau(p_0)]$, the policy $\Gamma^*=(\mathcal M^*,\pi^*)$ with $\mathcal M^*=\{m_0,m_1\}$ and
--   $$\pi^*(m_1\mid\omega=0)=\frac{1-p_0}{p_0}\,\frac{\xi(b_0-a_0)}{(a_1-a_0)-\xi(b_0-a_0)},\qquad \pi^*(m_1\mid\omega=1)=1 \tag{5}$$
--   is a policy and is optimal.
--
--   The theorem describes how much a retailer should reveal to an upstream supplier: everything when the critical ratio is high, nothing in an intermediate range, and, when the critical ratio is low, a partial signal that pools part of the wide-support state with the narrow-support state.
--
--   **Formalization Note** "Optimal" means optimal for (3): with some best-response profile, the policy's expected shortage is at most that of every policy on every finite message space under every best-response profile. At the interval endpoints two bullets apply and both policies are optimal, as the paper notes (p. 26). The hypotheses $0\le a_0$, $0\le a_1$ are added (nonnegative demand). With equal supports $\xi_h$ is $0/0=0$ in Lean and bullet 1 claims full disclosure for every $\xi$, which is true since then every policy has the same cost. At $p_0=1$ the factor $1-p_0=0$ makes $\pi^*(m_1\mid\omega=0)=0$ in Lean even where the second fraction's denominator vanishes; at $p_0=1$ every policy is optimal.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 9, Theorem 1, (5); p. 8, Proposition 1 (definition of τ̲)

import Mathlib
import Definitions.Def_SCInfoDesign_Nested_Setting

namespace SCInfoDesign.Nested
theorem theorem_1 (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) :
    (P.ξh ≤ P.ξ → P.IsOptimalPolicy p₀ fullDisclosure) ∧
    (P.τlow p₀ ≤ P.ξ → P.ξ ≤ P.ξh → P.IsOptimalPolicy p₀ noDisclosure) ∧
    (P.ξ ≤ P.τlow p₀ → P.IsOptimalPolicy p₀ (P.gammaStar p₀)) := by sorry
end SCInfoDesign.Nested
