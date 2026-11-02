-- Prove2me | Theorems.Thm_TestDistancing_Equilibrium_type_gap_mixed
-- name    : TestDistancing.Equilibrium.type_gap_mixed
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-02T03:17:17.171283+00:00
-- url     : https://prove2.me/theorems/90d3c418-8b00-400c-bfb2-f2e266697cbc
-- title:
--   Low and high types have asymptotically equal infection probability under any symmetric mixed profile
-- statement:
--   Consider the activity game of Acemoglu, Makhdoumi, Malekian and Ozdaglar with $n$ agents, under the standing assumptions $0\le v_L<v_H\le 1$, $0<\eta\le 1$, $0<\beta\le 1$, $0\le p<1$, $c>0$, $0<r_H<1$. The first $\lceil r_H n\rceil$ agents have high value and the rest low value. A type-symmetric mixed profile $\gamma=(\gamma_L,\gamma_H)\in[0,1]^2$ lets each low-value (high-value) agent be active independently with probability $\gamma_L$ ($\gamma_H$). For an agent $i$, write
--   $$P^{\mathrm{inf}}_i(x_i=1;\gamma;\alpha_L,\alpha_H)$$
--   for her infection probability when she is active and all other agents mix according to $\gamma$, under testing policy $(\alpha_L,\alpha_H)$.
--
--   **Claim.** For every $\varepsilon>0$ there is $M\in\mathbb N_+$ such that for all $n\ge M$, all policies $(\alpha_L,\alpha_H)\in[0,1]^2$, all profiles $\gamma\in[0,1]^2$, every low-value agent $l$ and every high-value agent $h$,
--   $$\Bigl|P^{\mathrm{inf}}_l(x_l=1;\gamma;\alpha_L,\alpha_H)-P^{\mathrm{inf}}_h(x_h=1;\gamma;\alpha_L,\alpha_H)\Bigr|<\varepsilon .$$
--
--   From the perspective of an active agent, the two situations differ only in the type of a single other agent. The claim therefore says that one agent's activity and testing probabilities have a vanishing effect on another agent's infection in a large society. With $\varepsilon<v_H-v_L$ it is the "large $n$" step the source uses repeatedly in the proof of Proposition 2: it excludes the candidate equilibria in which the low-value type is weakly more active than the high-value type.
--
--   **Formalization Note** The infection probability is the platform's `PinfMix P γ α i 1`, the expectation of `Pinf` over the other agents' independent Bernoulli activities with the agent's own activity set to one. $M$ is required to work uniformly over all policies and all profiles.
-- source:
--   Acemoglu, Makhdoumi, Malekian & Ozdaglar, Testing, Voluntary Social Distancing and the Spread of an Infection, NBER Working Paper 27483 (July 2020), https://www.nber.org/papers/w27483, Proof of Proposition 2, pp. 28–31 (PDF 30–33): the bound |P^inf_l − P^inf_h| < ε for n ≥ M (p. 28), and its uses 'for large enough n the difference between the left-hand [sides] ... becomes smaller than vH − vL' at mixed profiles (part (c), cases 2–3, p. 31) and 'follows from n being large' (part (b), case 4, p. 30)

import Mathlib
import Definitions.Def_TestDistancing_Equilibrium_Model

namespace TestDistancing.Equilibrium

/-- Under any type-symmetric mixed profile, a low- and a high-value agent who are active have
asymptotically equal infection probabilities, uniformly in the policy and the profile. -/
theorem type_gap_mixed (P : Params) (hP : P.Standing) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, M ≤ n → ∀ α ∈ PolicySquare,
      ∀ γ ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      ∀ l h : Fin n, ¬ IsHigh P l → IsHigh P h →
        |PinfMix P γ α l 1 - PinfMix P γ α h 1| < ε := by sorry

end TestDistancing.Equilibrium
