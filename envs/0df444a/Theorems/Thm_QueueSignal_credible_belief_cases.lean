-- Prove2me | Theorems.Thm_QueueSignal_credible_belief_cases
-- name    : QueueSignal.credible_belief_cases
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:06:49.461495+00:00
-- url     : https://prove2.me/theorems/1635d338-ad9c-47cd-897b-bb61b71002cc
-- title:
--   §3.2 — the credible updating rule forces the prior, $1$ or $0$, and puts no restriction when both types strictly prefer to stay
-- statement:
--   Consider the two-type signaling game with prior $0<\delta<1$ and an arbitrary payoff function $\pi(t,s,d)$. Fix a pure profile with beliefs, a signal $s$ off its equilibrium path, the equilibrium payoffs $u^*_t$, and a candidate posterior $\gamma$ after $s$.
--
--   1. If $\gamma$ is credible (Definition 2) and both types strictly prefer to deviate to $s$ under $\gamma$, then $\gamma=\delta$.
--   2. If $\gamma$ is credible, the high-quality type weakly prefers to deviate ($\pi(H,s,\gamma)\ge u^*_H$) and the low-quality type strictly prefers to stay ($\pi(L,s,\gamma)<u^*_L$), then $\gamma=1$.
--   3. If $\gamma$ is credible, the low-quality type weakly prefers to deviate and the high-quality type strictly prefers to stay, then $\gamma=0$.
--   4. If both types strictly prefer to stay under $\gamma$ (so $\mathbb T'\cup\mathbb T''=\emptyset$), then $\gamma$ is not credible: the credible updating rule puts no restriction on the off-path belief.
--
--   This is the form in which the credible updating rule is applied in the equilibrium analysis: it pins the off-path posterior to the prior, to $1$ or to $0$.
--
--   Differences from the source:
--   - generalization: "in our queueing setting" (payoffs λ^O, λ^U, the same for both types) → any payoff function π(t, s, d); reason: the argument uses only Definition 2; the queueing payoffs are an instance
--   - reading: Definition 2(b): T′ and T″ "remain unchanged under the above posterior belief" → T′ and T″ computed at the posterior γ itself; reason: the paper calls the procedure "essentially a fixed-point argument" (p.547)
--   - encoding: "the credible updating rule puts no restrictions on the off-equilibrium-path belief" when T′ ∪ T″ is empty → a γ under which both types strictly prefer to stay is not credible; reason: a perfect sequential equilibrium is tested only against credible beliefs, so such γ impose nothing
-- source:
--   Guo, Haviv, Luo, Wang, Signaling Service Quality Through Queue Disclosure, MSOM 25(2) (2023), doi:10.1287/msom.2022.1170, §3.2, paragraph after Definition 2, pp.547–548

import Mathlib
import Definitions.Def_QueueSignal_SignalingGame

namespace QueueSignal

/-- **The credible updating rule in the two-type game** (Guo, Haviv, Luo, Wang, *Signaling Service Quality Through Queue Disclosure*, MSOM 25(2) (2023),
doi:10.1287/msom.2022.1170, §3.2, paragraph after
Definition 2, pp.547–548, PDF pp.6–7).

Let `(σ, b)` be a pure profile with beliefs, `s` a signal off the equilibrium path, `u*_t` the
equilibrium payoffs and `γ` a credible posterior at `s` (Definition 2). Then

1. if both types strictly prefer to deviate under `γ`, then `γ = δ` (the prior);
2. if the high-quality type strictly prefers to deviate or is indifferent, and the low-quality
   type strictly prefers to stay, then `γ = 1`;
3. if the low-quality type strictly prefers to deviate or is indifferent, and the high-quality
   type strictly prefers to stay, then `γ = 0`;
4. if both types strictly prefer to stay under `γ` (`𝕋′ ∪ 𝕋″ = ∅`), then `γ` is not credible:
   the rule puts no restriction on the off-path belief.

Stated for an arbitrary type- and belief-dependent payoff `pay`. -/
theorem credible_belief_cases (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (pay : QType → Sig → ℝ → ℝ) (σ : Profile) (b : Sig → ℝ) (s : Sig) (hs : ¬ OnPath σ s)
    (γ : ℝ) :
    (IsCredible δ pay σ b s γ →
      (∀ t, eqPay pay σ b t < pay t s γ) → γ = δ) ∧
    (IsCredible δ pay σ b s γ →
      eqPay pay σ b .H ≤ pay .H s γ → pay .L s γ < eqPay pay σ b .L → γ = 1) ∧
    (IsCredible δ pay σ b s γ →
      eqPay pay σ b .L ≤ pay .L s γ → pay .H s γ < eqPay pay σ b .H → γ = 0) ∧
    ((∀ t, pay t s γ < eqPay pay σ b t) → ¬ IsCredible δ pay σ b s γ) := by sorry

end QueueSignal
