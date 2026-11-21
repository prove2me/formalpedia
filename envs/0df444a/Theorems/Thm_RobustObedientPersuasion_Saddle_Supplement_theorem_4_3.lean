-- Prove2me | Theorems.Thm_RobustObedientPersuasion_Saddle_Supplement_theorem_4_3
-- name    : RobustObedientPersuasion.Saddle.Supplement.theorem_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:26:57.433075+00:00
-- url     : https://prove2.me/theorems/5979ae6b-5012-4bfa-80f1-de1e2746e2b1
-- title:
--   Theorem 4.3 — robust obedience is free when the ℓ1 radius of P(α) is below γ/L_R
-- statement:
--   This is a companion theorem of the mission (local exactness of robust obedience); it is not a step in the proof of the goal, Theorem 3.1.
--
--   Let $\Omega$ and $A$ be finite, $u,v:\Omega\times A\to\mathbb R$ the Receiver's and Sender's utilities, and $\alpha\in\Delta(A)$ the observed action distribution with support $B$, such that no action in $B$ is statewise strictly dominated (every obedience region $M_a$, $a\in B$, is nonempty). Let $\mathcal P(\alpha)$ be the identified set, $\Pi_B$ the direct policies recommending only actions in $B$, $\Pi_{RO}(\alpha)$ the robustly obedient policies and $V(\pi\mid\mu)$ the robustly obedient Sender payoff.
--
--   In the **unrestricted problem** the Sender uses any policy $\pi:\Omega\to\Delta(S)$ with a finite message set $S$; after message $s$ the Receiver, who knows the prior $\mu$, picks a best response from
--   $$BR(\pi,s,\mu)=\arg\max_{a\in A}\sum_{\omega}\pi(s\mid\omega)\mu(\omega)u(a,\omega),$$
--   with ties broken in the Sender's favour, so the Sender's payoff is $V_{\mathrm{unr}}(\pi\mid\mu)=\sum_{s}\max_{a\in BR(\pi,s,\mu)}\sum_\omega\pi(s\mid\omega)\mu(\omega)v(a,\omega)$. Write
--   $$W(\alpha)=\sup_{S,\ \pi}\ \inf_{\mu\in\mathcal P(\alpha)}V_{\mathrm{unr}}(\pi\mid\mu),\qquad W_{RO}(\alpha)=\max_{\pi\in\Pi_{RO}(\alpha)}\ \min_{\mu\in\mathcal P(\alpha)}V(\pi\mid\mu).$$
--
--   Let $\bar p\in\mathcal P(\alpha)$ and let $\pi^*\in\Pi_B$ be an unrestricted maxmin-optimal direct policy: $\inf_{\mu\in\mathcal P(\alpha)}V_{\mathrm{unr}}(\pi^*\mid\mu)=W(\alpha)$. For $a\in B$, $a'\in A\setminus\{a\}$ and a prior $p$ define the obedience margin
--   $$D^{\pi^*}_{a,a'}(p)=\sum_{\omega\in\Omega}\pi^*(a\mid\omega)p(\omega)\,[u(a,\omega)-u(a',\omega)].$$
--   Suppose
--   $$\gamma:=\min_{a\in B,\ a'\in A\setminus\{a\}}D^{\pi^*}_{a,a'}(\bar p)>0,\qquad L_R:=\max_{a\in B,\ a'\in A\setminus\{a\},\ \omega\in\Omega}|u(a,\omega)-u(a',\omega)|>0,$$
--   and let $r_1(\mathcal P(\alpha),\bar p)=\sup_{p\in\mathcal P(\alpha)}\|p-\bar p\|_1$ with $\|x\|_1=\sum_\omega|x(\omega)|$. If
--   $$r_1(\mathcal P(\alpha),\bar p)<\frac{\gamma}{L_R},$$
--   then $\pi^*\in\Pi_{RO}(\alpha)$ and $W_{RO}(\alpha)=W(\alpha)$.
--
--   The theorem says that robust obedience costs the Sender nothing when the identified set is small relative to the optimal policy's incentive margin: the threshold $\gamma/L_R$ is the amount of prior uncertainty the Receiver's incentives can absorb.
--
--   **Formalization Note** The unrestricted value ranges over message sets $\mathrm{Fin}\,m$, $m\in\mathbb N$. Best responses use the unnormalized objective, so no division by a message probability occurs. The minimum $\gamma$, the maximum $L_R$, the radius and the two values are real `sInf`/`sSup` of finite or bounded nonempty sets; empty index sets give $0$, which the positivity hypotheses exclude.
--
--   Differences from the source:
--   - reading: no action in supp(α) is statewise strictly dominated under u (maintained throughout, p. 3) → every M_a with α(a) > 0 is nonempty (published predicate NoSupportedActionDominated); reason: the paper states (p. 3) that the condition is equivalent to the existence of a posterior under which each supported action is optimal; this is the meaning used by the published base mission
--   - generalization: the model assumes a true prior μ₀ ∈ int Δ(Ω) rationalizing α → no μ₀ appears; reason: μ₀ enters neither P(α), the policies, the payoffs, W(α), W_RO(α) nor the conclusion, so the Lean statement covers every instance of the source and specializes to it
--   - reading: the unrestricted problem's Receiver action a*(s, μ) ∈ argmax of posterior expected utility (p. 2), selection unspecified there → Sender-preferred selection from the best-response set computed with the unnormalized objective ∑_ω π(s|ω)μ(ω)u(a,ω): V_unr(π|μ) = ∑_s max_{a ∈ BR(π,s,μ)} ∑_ω π(s|ω)μ(ω)v(a,ω); reason: footnote 3 (p. 3) says the unrestricted problem of [Ros26] uses a Sender-preferred selection; Appendix B uses the unnormalized argmax, which equals the posterior argmax for messages of positive probability, and a zero-probability message contributes 0 whatever action is selected
--   - encoding: W(α): supremum over all finite message sets S and policies π : Ω → Δ(S) of the worst case over P(α) → sSup over m ∈ ℕ and policies π : Ω → Fin m → ℝ of sInf_{μ ∈ P(α)} V_unr(π|μ); reason: every finite S is in bijection with some Fin m and V_unr is invariant under relabelling messages; the inner problem is an infimum because V_unr is only upper semicontinuous in μ; both sets are nonempty and bounded (|V_unr| ≤ max|v| on Δ(Ω), p̄ ∈ P(α)), so sSup/sInf are the true sup/inf
--   - encoding: unrestricted maxmin-optimal direct policy π* ∈ Π_B → π* ∈ supportedPolicies α (messages = A) with sInf_{μ ∈ P(α)} V_unr(π*|μ) = W(α); reason: direct policy means message a = recommendation a; optimality means attaining the unrestricted value
--   - encoding: W_RO(α) = max_{π ∈ Π_RO(α)} min_{μ ∈ P(α)} V(π|μ) → sSup over π ∈ Π_RO(α) of sInf_{μ ∈ P(α)} senderPayoff; reason: the extrema are attained by Theorem 3.1 when Π_RO(α) ≠ ∅, which each theorem's conclusion supplies; on these instances sSup/sInf equal max/min
--   - encoding: u(a, ω), v(a, ω), π(a | ω), ‖·‖₁ → state-first arrays u ω a, v ω a, π ω a; l1Dist p q = ∑_ω |p ω − q ω|; reason: the published base model's indexing convention; the ℓ1 norm is written out (not Mathlib's sup norm), same instances
--   - encoding: γ := min_{a ∈ B, a' ∈ A∖{a}} D^{π*}_{a,a'}(p̄) > 0 and L_R := max_{a ∈ B, a' ∈ A∖{a}, ω} |u(a,ω) − u(a',ω)| > 0 → incentiveMargin (real sInf) and utilityRange (real sSup) of the finite index sets, with hypotheses 0 < incentiveMargin and 0 < utilityRange; reason: for a finite nonempty index set sInf/sSup are the min/max; the empty index set (|A| = 1) gives the value 0, which the positivity hypotheses exclude, as the source's '> 0' does
-- source:
--   Shabab Neel, Robustly Obedient Data Driven Persuasion under State-dependent Sender Payoffs, STOC 2027 submission #51 (October 2026), PDF SHA-256 c8d16d8d566dd78eea1f7db42ce72f49000256f933311c4daac2de1df952b40d, Theorem 4.3, PDF p. 5; proof in Appendix G, PDF pp. 9–10

import Mathlib
import Definitions.Def_RobustObedientPersuasion_Saddle_Model
import Definitions.Def_RobustObedientPersuasion_Saddle_Supplement_Unrestricted

namespace RobustObedientPersuasion.Saddle.Supplement

/-- Neel, STOC 2027 submission #51, Theorem 4.3 (PDF p. 5): local exactness of robust
obedience. -/
theorem theorem_4_3 {Ω A : Type*} [Fintype Ω] [Fintype A]
    (u v : Ω → A → ℝ) (α : A → ℝ) (hα : α ∈ stdSimplex ℝ A)
    (hdom : NoSupportedActionDominated u α)
    (pbar : Ω → ℝ) (hpbar : pbar ∈ identifiedSet u α)
    (πstar : Ω → A → ℝ) (hopt : IsUnrestrictedMaxminOptimalDirect u v α πstar)
    (hγ : 0 < incentiveMargin u α πstar pbar)
    (hLR : 0 < utilityRange u α)
    (hr : uncertaintyRadius u α pbar < incentiveMargin u α πstar pbar / utilityRange u α) :
    πstar ∈ robustlyObedientPolicies u α ∧ robustValue u v α = unrestrictedValue u v α := by sorry

end RobustObedientPersuasion.Saddle.Supplement
