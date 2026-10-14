-- Prove2me | Theorems.Thm_SCInfoDesign_Disjoint_theorem_3
-- name    : SCInfoDesign.Disjoint.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:50.418881+00:00
-- url     : https://prove2.me/theorems/1e64b961-1acf-4746-9eeb-788d1eaa5b36
-- title:
--   Theorem 3, p. 16 — disjoint supports: full disclosure if 2(b₀ − a₀) ≥ b₁ − a₁; else no disclosure for p₀ ≥ p̃ and Γ*_DS of (8) for p₀ < p̃
-- statement:
--   A retailer knows the state $\omega\in\{0,1\}$, with prior $p_0=\mathbb P(\omega=0)\in[0,1]$; her demand is $D_0\sim U[a_0,b_0]$ in state $0$ and $D_1\sim U[a_1,b_1]$ in state $1$. Assume $a_0<b_0$, $a_1<b_1$, $0\le a_0$, $0\le a_1$, $0<\xi<1$, and that the supports are disjoint, $a_0>b_1$. She commits to a disclosure policy; a supplier with critical ratio $\xi$ observes the message, forms the posterior by Bayes' rule and produces an optimal newsvendor quantity; the retailer bears the expected shortage. A policy is *optimal* if, with a suitable best response of the supplier, its expected shortage is at most that of every finite-message policy under every best response, as in (3). Let
--   $$\tilde p=\max\Big(1-\xi,\ \frac{2(b_0-a_0)}{b_1-a_1}\Big).$$
--   Then:
--
--   1. if $2(b_0-a_0)\ge b_1-a_1$, full disclosure is optimal;
--   2. if $b_1-a_1>2(b_0-a_0)$, then no disclosure is optimal whenever $p_0\ge\tilde p$, and whenever $p_0<\tilde p$ the policy $\Gamma^*_{DS}$ with messages $m_0,m_1$ and
--   $$\pi^*_{DS}(m_0\mid\omega=0)=1,\qquad \pi^*_{DS}(m_0\mid\omega=1)=\frac{1-\tilde p}{\tilde p}\cdot\frac{p_0}{1-p_0}\qquad(8)$$
--   is optimal (and is a policy).
--
--   The theorem shows that with disjoint supports the optimal policy depends on the critical ratio only through the threshold $\tilde p$, and that full disclosure is optimal for every $\xi$ when the high-demand support is at least half as wide as the low-demand one.
--
--   **Formalization Note** The paper states "there exists $\tilde p$ … Furthermore, $\tilde p=\max(\dots)$"; the formalization gives $\tilde p$ explicitly. Optimality is over all finite message spaces and all best-response profiles, and the optimal policy may be paired with the best response the retailer prefers (the joint minimization over $\Gamma$ and $Q^*\in\mathcal B(\Gamma)$ in (3), footnote 9); at $p=1-\xi$ the supplier is indifferent over $[b_1,a_0]$ and the theorem needs this choice. The cost (2) is normalized by $C_s+C_e$, and no disclosure is the one-message policy. The hypotheses $a_0<b_0$, $a_1<b_1$, $0\le a_0$, $0\le a_1$, $0<\xi<1$ are the paper's implicit standing assumptions.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 16, Theorem 3, (8)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Disjoint_Setting

namespace SCInfoDesign.Disjoint

/-- Theorem 3 (p. 16): the retailer's optimal policy with disjoint supports `a₀ > b₁`.
Full disclosure if `2(b₀ - a₀) ≥ b₁ - a₁`; otherwise no disclosure for `p₀ ≥ p̃` and `Γ*_DS` of
(8) for `p₀ < p̃`, where `p̃ = max(1 - ξ, 2(b₀ - a₀)/(b₁ - a₁))`. -/
theorem theorem_3 (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hξ₀ : 0 < P.ξ) (hξ₁ : P.ξ < 1) (hdisj : P.b₁ < P.a₀)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) :
    (P.b₁ - P.a₁ ≤ 2 * (P.b₀ - P.a₀) → IsOptimalPolicy P p₀ SCInfoDesign.Nested.fullDisclosure) ∧
    (2 * (P.b₀ - P.a₀) < P.b₁ - P.a₁ →
      (P.ptilde ≤ p₀ → IsOptimalPolicy P p₀ SCInfoDesign.Nested.noDisclosure) ∧
      (p₀ < P.ptilde → IsOptimalPolicy P p₀ (P.gammaStarDS p₀))) := by sorry

end SCInfoDesign.Disjoint
