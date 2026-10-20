-- Prove2me | Theorems.Thm_PrivacyQueue_Control_theorem_1
-- name    : PrivacyQueue.Control.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:24.249647+00:00
-- url     : https://prove2.me/theorems/ada35607-c0a1-43a6-8dca-b61551d22e49
-- title:
--   Theorem 1 — customer control versus full disclosure under SPT and LPT priority
-- statement:
--   Consider the paper's stable single-server queue and any equilibrium disclosure probability $\gamma^*$. Let $CS_{\rm control}$ be total customer surplus when customers choose whether to disclose their type, and let $CS_{\rm discl}$ be surplus under compulsory full disclosure. Then
--
--   $$\sigma<1\quad\Longrightarrow\quad CS_{\rm control}\le CS_{\rm discl},$$
--   $$\sigma>1\quad\Longrightarrow\quad CS_{\rm control}\ge CS_{\rm discl}.$$
--
--   In either case the comparison is strict when $\gamma^*<1$ and $\alpha>0$: some customers withhold information and type-$H$ requests occur with positive probability. The result identifies how the fixed priority order $H>N>L$ changes the social effect of customer control.
--
--   **Formalization Note** The paper selects the Pareto-dominant equilibrium; the formal statement holds for every equilibrium satisfying its endpoint or stable-interior definition, and therefore includes that selection. Positive $\mu$, $\lambda$, and $c$ are explicit rate/cost assumptions. The strict clauses add $\alpha>0$: at $\alpha=0$, $\gamma^*=0$ may be an equilibrium while the two surplus values coincide.
-- source:
--   Hu, Momot & Wang, Privacy Management in Service Systems, submitted manuscript (draft of 12 Feb 2022; SSRN 3628751), p. 15 (PDF 16), Theorem 1; Online Appendix p. 3 (PDF 37), A.3

import Mathlib
import Definitions.Def_PrivacyQueue_Control_Model

namespace PrivacyQueue.Control

/-- Theorem 1, p. 15: customer control compared with compulsory disclosure. -/
theorem theorem_1 (P : Params) (hS : P.Standing) (γs : ℝ)
    (hEq : IsEquilibrium P γs) :
    (P.σ < 1 → CScontrol P γs ≤ CSdiscl P ∧
      (γs < 1 → 0 < P.α → CScontrol P γs < CSdiscl P)) ∧
    (1 < P.σ → CSdiscl P ≤ CScontrol P γs ∧
      (γs < 1 → 0 < P.α → CSdiscl P < CScontrol P γs)) := by sorry

end PrivacyQueue.Control
