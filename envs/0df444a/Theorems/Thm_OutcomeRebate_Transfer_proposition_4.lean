-- Prove2me | Theorems.Thm_OutcomeRebate_Transfer_proposition_4
-- name    : OutcomeRebate.Transfer.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:59.162959+00:00
-- url     : https://prove2.me/theorems/5b25c06b-2437-43a4-90ee-140493d14ed7
-- title:
--   Proposition 4, p. 23 (PDF 24) — under Assumption 2, a firm-to-payer transfer makes outcome-based pricing better for both iff q < q0 (when v′ < M′)
-- statement:
--   Suppose Assumptions 1 and 2 hold, with $q_1 \in (0,1)$ the solution of $zq = 2/\beta$, and let $p^U$, $p^O$ be equilibrium prices under uniform and outcome-based pricing. Write
--   $$\Delta\Pi = \Pi^O_{\text{firm}}(p^O) - \Pi^U_{\text{firm}}(p^U), \qquad \Delta W = W^O_{\text{payer}}(p^O) - W^U_{\text{payer}}(p^U)$$
--   for the firm's and the payer's gains from outcome-based pricing, each at the payer's coverage response.
--
--   1. If $v' > M'$, the firm's and the payer's interests are aligned: $\Delta\Pi > 0 \iff \Delta W > 0$, and $\Delta\Pi < 0 \iff \Delta W < 0$.
--   2. If $v' < M'$, there is a transfer $\tau \in \mathbb R$ from the firm to the payer that makes outcome-based pricing strictly better than uniform pricing for both parties,
--   $$\Pi^U_{\text{firm}}(p^U) < \Pi^O_{\text{firm}}(p^O) - \tau \quad\text{and}\quad W^U_{\text{payer}}(p^U) < W^O_{\text{payer}}(p^O) + \tau,$$
--   if and only if the drug is high-risk, $q < q_0$.
--   3. If $v' < M'$ and $q < q_0$, then
--   $$0 < W^U_{\text{payer}} - W^O_{\text{payer}} < \Pi^O_{\text{firm}} - \Pi^U_{\text{firm}},$$
--   so every transfer strictly between these two amounts, which is positive and therefore from the firm to the payer, works.
--
--   Outcome-based pricing combined with a side payment can benefit both parties, but only for high-risk drugs.
--
--   **Formalization Note** The payer's side is its objective $W_{\text{payer}}$ (payoff plus total patient payoff), as in the paper's proof. "Better for both" is read as strict improvement for both parties. The page's range "from $W^U_{\text{payer}} - W^O_{\text{payer}}$ up to $\Pi^O_{\text{firm}} - \Pi^U_{\text{firm}}$" includes its endpoints, where one party is only indifferent, so clause 3 states the open range. The statement is about every pair of equilibrium prices of the backward-induction game, not about $p^*$ and $\tilde p^*$ directly. The case $v' = M'$ is excluded, as on the page. At $q = q_0$ every difference vanishes and the equivalence in clause 2 still holds.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), p. 23 (PDF 24), Proposition 4

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer

/-- Proposition 4 (p. 23). Suppose Assumption 2 holds, and let `p^U`, `p^O` be equilibrium prices under
uniform and outcome-based pricing. Write `ΔΠ` for the firm's gain and `ΔW` for the payer's gain
(in its objective) from outcome-based pricing.
1. If `v′ > M′`, the interests are aligned: `ΔΠ > 0 ↔ ΔW > 0` and `ΔΠ < 0 ↔ ΔW < 0`.
2. If `v′ < M′`, a transfer `τ` from the firm to the payer making outcome-based pricing strictly
better for both (`Π^U < Π^O − τ` and `W^U < W^O + τ`) exists iff `q < q₀`.
3. If `v′ < M′` and `q < q₀`, then `0 < W^U − W^O < Π^O − Π^U`, so every transfer strictly between
these two amounts works. -/
theorem proposition_4 (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (q1 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β) (hA2 : Assumption2 P q1)
    (pU pO : ℝ) (hU : IsEqPriceU P pU) (hO : IsEqPriceO P pO) :
    let dPi := realizedProfitO P pO - realizedProfitU P pU
    let dW := realizedObjO P pO - realizedObjU P pU
    (Mprime P < P.vp → ((0 < dPi ↔ 0 < dW) ∧ (dPi < 0 ↔ dW < 0))) ∧
    (P.vp < Mprime P →
      ((∃ τ : ℝ, realizedProfitU P pU < realizedProfitO P pO - τ ∧
          realizedObjU P pU < realizedObjO P pO + τ) ↔ P.q < q0 P.α P.lam)) ∧
    (P.vp < Mprime P → P.q < q0 P.α P.lam → 0 < -dW ∧ -dW < dPi) := by sorry

end OutcomeRebate.Transfer
