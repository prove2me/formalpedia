-- Prove2me | Theorems.Thm_SeqExpDiffusion_theorem_2_crossing_gain
-- name    : SeqExpDiffusion.theorem_2_crossing_gain
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:01.4993+00:00
-- url     : https://prove2.me/theorems/e928ac6e-6f5d-4a25-b74a-ec65197f153c
-- title:
--   Proof of Theorem 2, case 2, p.54 — strict gain at the crossing of two rewards
-- statement:
--   Let $r>0$, $\tilde\sigma>0$, and let $a_i,a_k$ be two actions whose rewards have different slopes and cross at $\delta_\star=\hat\delta_{ik}\in(0,1)$, i.e. $\tilde R_i(\delta_\star)=\tilde R_k(\delta_\star)$. If $\tilde{\mathcal G}_{ik}$ is the value function of (12) with the two-action payoff $\tilde G_{ik}$, then
--
--   $$\tilde R_i(\delta_\star)<\tilde{\mathcal G}_{ik}(\delta_\star).$$
--
--   At a belief where two actions are equally good, experimenting is strictly better than stopping; the proof of Theorem 2 uses this to rule out a kink of $\tilde V$ in the intervention regions.
--
--   Differences from the source:
--   - generalization: a pair with G̃_ik ≥ 0, whose value is the closed form of Proposition 5 → any two actions with different slopes crossing in (0, 1), of any sign, with 𝒢̃_ik the value function of (12); reason: the closed form is that value function (p.21), so the statement specializes to the page
--   - generalization: stopping times of the filtration 𝔽 of the experimentation history (p.8) → every probability space and every filtration for which the driving motion is Brownian; reason: the paper's setting is one instance, so the statement specializes to it
--   - reading: (12) is silent on the event τ = ∞ → the reward is 0 on {τ = ∞}; reason: the payoffs are bounded, so this changes no supremum relative to finite stopping times
--   - encoding: r and σ̃ are a discount rate and a volatility, with no stated sign → r > 0 and σ̃ > 0; reason: the paper uses both silently (γ needs σ̃ ≠ 0, and r = 0 gives γ = 1); only degenerate cases are excluded
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, proof of Theorem 2, case 2, p.54

import Definitions.Def_SeqExpDiffusion_reward
import Definitions.Def_SeqExpDiffusion_pairPayoff
import Definitions.Def_SeqExpDiffusion_IsValueFunction

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SeqExpDiffusion

/-- Strict gain at the crossing point, proof of Theorem 2, case 2, Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, p.54: if `δ⋆ = δ̂_ik` is
the intersection point of `R̃_i` and `R̃_k`, then "from Proposition 5 we have that
`R̃_i(δ⋆) < 𝒢̃_ik(δ⋆)`".

For two actions whose rewards have different slopes and cross at `δ̂ ∈ (0, 1)`, the two-action value
exceeds the common reward at `δ̂`.

**Formalization Note** `𝒢̃_ik` is the value function of (12) with payoff `G̃_ik` (`IsValueFunction`),
which is what Proposition 5 and p.21 make it. No sign condition on the payoff is needed. -/
theorem theorem_2_crossing_gain {ι : Type*} (α β : ι → ℝ) (i k : ι) (r σ : ℝ) (hr : 0 < r)
    (hσ : 0 < σ) (hβ : β i ≠ β k) (δh : ℝ) (hδh : δh ∈ Ioo (0 : ℝ) 1)
    (hcross : reward α β i δh = reward α β k δh) (v : ℝ → ℝ)
    (hv : IsValueFunction r σ (pairPayoff α β i k) v) :
    reward α β i δh < v δh := by sorry

end SeqExpDiffusion
