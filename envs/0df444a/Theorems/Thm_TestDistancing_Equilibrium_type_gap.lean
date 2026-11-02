-- Prove2me | Theorems.Thm_TestDistancing_Equilibrium_type_gap
-- name    : TestDistancing.Equilibrium.type_gap
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-02T03:05:16.356592+00:00
-- url     : https://prove2.me/theorems/ca347e2a-f163-44a3-b3e7-866df4c49625
-- title:
--   Low and high types have asymptotically equal infection probability at full activity
-- statement:
--   Consider the infection model of Acemoglu, Makhdoumi, Malekian and Ozdaglar with $n$ agents, under the standing assumptions $0\le v_L<v_H\le 1$, $0<\eta\le 1$, $0<\beta\le 1$, $0\le p<1$, $c>0$, $0<r_H<1$. The first $\lceil r_H n\rceil$ agents have high value and the rest low value. Under a testing policy $(\alpha_L,\alpha_H)\in[0,1]^2$, each agent is tested independently with probability $\alpha_L$ or $\alpha_H$ according to her type. When every agent is fully active, links form independently with probability $\eta$, and an infected agent transmits along each link with probability $\beta p$ if tested and $\beta$ otherwise, starting from a uniformly random source. Write $P^{\mathrm{inf}}_i(\mathbf 1;\alpha_L,\alpha_H)$ for the probability that agent $i$ is infected.
--
--   **Claim.** For every $\varepsilon>0$ there is $M\in\mathbb N_+$ such that for all $n\ge M$, every policy $(\alpha_L,\alpha_H)\in[0,1]^2$, every low-value agent $l$ and every high-value agent $h$,
--   $$\bigl|P^{\mathrm{inf}}_l(\mathbf 1;\alpha_L,\alpha_H)-P^{\mathrm{inf}}_h(\mathbf 1;\alpha_L,\alpha_H)\bigr|<\varepsilon .$$
--
--   The two probabilities differ only through a single other agent whose testing probability is $\alpha_L$ in one case and $\alpha_H$ in the other, so the claim says that one agent's testing probability has a vanishing effect on any other agent's infection in a large society. The source uses it, with $\varepsilon<v_H-v_L$, to show that the low-value constraint of $A_1$ is the first to be violated, so that the regions $A_1,\dots,A_4$ cover all policies.
--
--   **Formalization Note** $P^{\mathrm{inf}}$ is the platform's `Pinf` at the all-ones profile `prof P 1 1`; $M$ is required to work uniformly over all policies in $[0,1]^2$.
-- source:
--   Acemoglu, Makhdoumi, Malekian & Ozdaglar, Testing, Voluntary Social Distancing and the Spread of an Infection, NBER Working Paper 27483 (July 2020), https://www.nber.org/papers/w27483, Proof of Proposition 2, part (b), p. 28 (PDF 30): 'For any ε > 0, there exists M ∈ N+ such that for n ≥ M, we have |P^inf_l(x_H = 1, x_L = 1, α_H, α_L) − P^inf_h(x_H = 1, x_L = 1, α_H, α_L)| < ε'; see also footnote 2 on p. 12

import Mathlib
import Definitions.Def_TestDistancing_Equilibrium_Model

namespace TestDistancing.Equilibrium

/-- At full activity, low- and high-value agents have asymptotically equal infection
probabilities, uniformly in the testing policy. -/
theorem type_gap (P : Params) (hP : P.Standing) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, M ≤ n → ∀ α ∈ PolicySquare,
      ∀ l h : Fin n, ¬ IsHigh P l → IsHigh P h →
        |Pinf P (prof P 1 1) α l - Pinf P (prof P 1 1) α h| < ε := by sorry

end TestDistancing.Equilibrium
