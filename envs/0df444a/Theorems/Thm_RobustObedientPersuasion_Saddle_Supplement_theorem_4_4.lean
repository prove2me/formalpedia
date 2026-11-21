-- Prove2me | Theorems.Thm_RobustObedientPersuasion_Saddle_Supplement_theorem_4_4
-- name    : RobustObedientPersuasion.Saddle.Supplement.theorem_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:27:25.323102+00:00
-- url     : https://prove2.me/theorems/736a2fc1-5b82-4184-805d-4aa75fec5408
-- title:
--   Theorem 4.4 — robustification by mixing with an interior policy, and the gap bound 0 ≤ W − W_RO ≤ (2M_vL_R/η)·r_1
-- statement:
--   This is a companion theorem of the mission (robustification by mixing and the payoff gap); it is not a step in the proof of the goal, Theorem 3.1.
--
--   Work in the setting of Theorem 4.3: finite $\Omega$, $A$, utilities $u,v$, an observed $\alpha\in\Delta(A)$ with support $B$ in which no supported action is statewise strictly dominated, the identified set $\mathcal P(\alpha)$, the policy classes $\Pi_B\supseteq\Pi_{RO}(\alpha)$, the robust payoff $V(\pi\mid\mu)$, the unrestricted payoff $V_{\mathrm{unr}}$ with the Sender-preferred selection from the Receiver's best responses, the values $W(\alpha)$ and $W_{RO}(\alpha)$, and the obedience margins $D^\pi_{a,a'}(p)=\sum_\omega\pi(a\mid\omega)p(\omega)[u(a,\omega)-u(a',\omega)]$. Let
--   $$L_R=\max_{a\in B,\ a'\in A\setminus\{a\},\ \omega}|u(a,\omega)-u(a',\omega)|,\qquad M_v=\max_{a\in B,\ \omega}|v(a,\omega)|.$$
--
--   Let $\bar p\in\mathcal P(\alpha)$ and $r_1=\sup_{p\in\mathcal P(\alpha)}\|p-\bar p\|_1$. Let $\pi^*\in\Pi_B$ be an unrestricted maxmin-optimal direct policy that is obedient at $\bar p$, i.e. $D^{\pi^*}_{a,a'}(\bar p)\ge0$ for all $a\in B$, $a'\ne a$. Suppose $\pi_{\mathrm{int}}\in\Pi_B$ satisfies $D^{\pi_{\mathrm{int}}}_{a,a'}(p)\ge\eta>0$ for all $a\in B$, $a'\ne a$ and $p\in\mathcal P(\alpha)$. Put
--   $$\delta=\frac{L_R\,r_1}{\eta+L_R\,r_1},\qquad \pi_\delta=(1-\delta)\pi^*+\delta\,\pi_{\mathrm{int}}.$$
--
--   1. **Policy robustification.** $\pi_\delta\in\Pi_{RO}(\alpha)$.
--   2. **Payoff bound under Receiver Action Stability.** Suppose that for every $a\in B$ and $p\in\mathcal P(\alpha)$, the Receiver's (Sender-preferred) action after recommendation $a$ under prior $p$ is $a$, both under $\pi_\delta$ and under $\pi^*$. Then
--   $$0\le W(\alpha)-W_{RO}(\alpha)\le\frac{2M_vL_R}{\eta}\,r_1(\mathcal P(\alpha),\bar p).$$
--
--   The theorem covers the intermediate regime left open by Theorem 4.3: when the optimal policy is only weakly obedient at the nominal prior but some policy is uniformly obedient with slack $\eta$, mixing yields a robustly obedient policy, and the welfare loss of robust obedience is at most linear in the $\ell_1$ radius of the identified set.
--
--   **Formalization Note** $\delta$ and $\pi_\delta$ are written out by `let` in the statement. $L_R$ and $M_v$ are real `sSup` of finite index sets, with value $0$ on an empty index set. Receiver Action Stability is the hypothesis that $a$ is a best response to recommendation $a$ attaining the Sender's maximum over the best-response set, for both policies; it is a hypothesis of part 2 only, and all other hypotheses are common to both parts.
--
--   Differences from the source:
--   - reading: no action in supp(α) is statewise strictly dominated under u (maintained throughout, p. 3) → every M_a with α(a) > 0 is nonempty (published predicate NoSupportedActionDominated); reason: the paper states (p. 3) that the condition is equivalent to the existence of a posterior under which each supported action is optimal; this is the meaning used by the published base mission
--   - generalization: the model assumes a true prior μ₀ ∈ int Δ(Ω) rationalizing α → no μ₀ appears; reason: μ₀ enters neither P(α), the policies, the payoffs, W(α), W_RO(α) nor the conclusion, so the Lean statement covers every instance of the source and specializes to it
--   - reading: the unrestricted problem's Receiver action a*(s, μ) ∈ argmax of posterior expected utility (p. 2), selection unspecified there → Sender-preferred selection from the best-response set computed with the unnormalized objective ∑_ω π(s|ω)μ(ω)u(a,ω): V_unr(π|μ) = ∑_s max_{a ∈ BR(π,s,μ)} ∑_ω π(s|ω)μ(ω)v(a,ω); reason: footnote 3 (p. 3) says the unrestricted problem of [Ros26] uses a Sender-preferred selection; Appendix B uses the unnormalized argmax, which equals the posterior argmax for messages of positive probability, and a zero-probability message contributes 0 whatever action is selected
--   - encoding: W(α): supremum over all finite message sets S and policies π : Ω → Δ(S) of the worst case over P(α) → sSup over m ∈ ℕ and policies π : Ω → Fin m → ℝ of sInf_{μ ∈ P(α)} V_unr(π|μ); reason: every finite S is in bijection with some Fin m and V_unr is invariant under relabelling messages; the inner problem is an infimum because V_unr is only upper semicontinuous in μ; both sets are nonempty and bounded (|V_unr| ≤ max|v| on Δ(Ω), p̄ ∈ P(α)), so sSup/sInf are the true sup/inf
--   - encoding: unrestricted maxmin-optimal direct policy π* ∈ Π_B → π* ∈ supportedPolicies α (messages = A) with sInf_{μ ∈ P(α)} V_unr(π*|μ) = W(α); reason: direct policy means message a = recommendation a; optimality means attaining the unrestricted value
--   - encoding: W_RO(α) = max_{π ∈ Π_RO(α)} min_{μ ∈ P(α)} V(π|μ) → sSup over π ∈ Π_RO(α) of sInf_{μ ∈ P(α)} senderPayoff; reason: the extrema are attained by Theorem 3.1 when Π_RO(α) ≠ ∅, which each theorem's conclusion supplies; on these instances sSup/sInf equal max/min
--   - encoding: u(a, ω), v(a, ω), π(a | ω), ‖·‖₁ → state-first arrays u ω a, v ω a, π ω a; l1Dist p q = ∑_ω |p ω − q ω|; reason: the published base model's indexing convention; the ℓ1 norm is written out (not Mathlib's sup norm), same instances
--   - encoding: L_R := max_{a ∈ B, a' ∈ A∖{a}, ω} |u(a,ω) − u(a',ω)|, M_v := max_{a ∈ B, ω} |v(a,ω)| → utilityRange and senderBound as real sSup of the finite index sets, 0 for an empty index set; reason: for a finite nonempty index set sSup is the max; the empty case (|A| = 1) occurs only where the source's maximum is over an empty set, and 0 is the value that keeps δ and C defined
--   - generalization: L_R is introduced in Theorem 4.3 together with the condition L_R > 0 → Theorem 4.4 assumes no positivity of L_R; reason: Theorem 4.4 does not state L_R > 0; if L_R = 0 then δ = 0, π_δ = π*, every margin of π* is identically 0, and both claims still hold, so the Lean statement specializes to the source's whenever L_R > 0
--   - reading: Receiver Action Stability: a*(a, p; π_δ) = a*(a, p; π*) = a, with a* the Sender-preferred best response → for every a ∈ B and p ∈ P(α), under both π_δ and π*, a is a best response to recommendation a and attains the Sender's maximum over the best-response set (ReceiverActionStable); reason: when several best responses give the Sender the same payoff the selection is not pinned down by the source; any selection that picks a satisfies the Lean condition, so the Lean hypothesis is implied by every reading of the source's
-- source:
--   Shabab Neel, Robustly Obedient Data Driven Persuasion under State-dependent Sender Payoffs, STOC 2027 submission #51 (October 2026), PDF SHA-256 c8d16d8d566dd78eea1f7db42ce72f49000256f933311c4daac2de1df952b40d, Theorem 4.4, PDF p. 5; proof in Appendix H, PDF p. 10

import Mathlib
import Definitions.Def_RobustObedientPersuasion_Saddle_Model
import Definitions.Def_RobustObedientPersuasion_Saddle_Supplement_Unrestricted

namespace RobustObedientPersuasion.Saddle.Supplement

/-- Neel, STOC 2027 submission #51, Theorem 4.4 (PDF p. 5): (i) policy robustification by
mixing with a uniformly obedient policy, and (ii) the payoff bound under Receiver Action
Stability. Here `δ = L_R r_1 / (η + L_R r_1)` and `π_δ = (1 - δ) π* + δ π_int`. -/
theorem theorem_4_4 {Ω A : Type*} [Fintype Ω] [Fintype A]
    (u v : Ω → A → ℝ) (α : A → ℝ) (hα : α ∈ stdSimplex ℝ A)
    (hdom : NoSupportedActionDominated u α)
    (pbar : Ω → ℝ) (hpbar : pbar ∈ identifiedSet u α)
    (πstar : Ω → A → ℝ) (hopt : IsUnrestrictedMaxminOptimalDirect u v α πstar)
    (hobed : ∀ a ∈ supp α, ∀ a' : A, a' ≠ a → 0 ≤ obedienceMargin u πstar a a' pbar)
    (πint : Ω → A → ℝ) (hint : πint ∈ supportedPolicies α) (η : ℝ) (hη : 0 < η)
    (hintη : ∀ a ∈ supp α, ∀ a' : A, a' ≠ a → ∀ p ∈ identifiedSet u α,
      η ≤ obedienceMargin u πint a a' p) :
    let δ := utilityRange u α * uncertaintyRadius u α pbar /
      (η + utilityRange u α * uncertaintyRadius u α pbar)
    let πδ : Ω → A → ℝ := fun ω a => (1 - δ) * πstar ω a + δ * πint ω a
    -- (i) Policy Robustification
    πδ ∈ robustlyObedientPolicies u α ∧
    -- (ii) Payoff Bound under Receiver Action Stability
    (ReceiverActionStable u v α πstar πδ →
      0 ≤ unrestrictedValue u v α - robustValue u v α ∧
      unrestrictedValue u v α - robustValue u v α ≤
        (2 * senderBound v α * utilityRange u α / η) * uncertaintyRadius u α pbar) := by sorry

end RobustObedientPersuasion.Saddle.Supplement
