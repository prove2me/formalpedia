-- Prove2me | Theorems.Thm_TestDistancing_Equilibrium_regions_cover
-- name    : TestDistancing.Equilibrium.regions_cover
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-02T02:53:16.413669+00:00
-- url     : https://prove2.me/theorems/e97af196-080d-4cae-8e20-6216ad98df8c
-- title:
--   Regions $A_1,\dots,A_4$ cover the policy square for large $n$
-- statement:
--   Consider the activity game of Acemoglu, Makhdoumi, Malekian and Ozdaglar with $n$ agents, of whom the first $\lceil r_H n\rceil$ have high value $v_H$ and the rest low value $v_L$, under the standing assumptions $0\le v_L<v_H\le 1$, $0<\eta\le 1$, $0<\beta\le 1$, $0\le p<1$, $c>0$, $0<r_H<1$. A testing policy is a pair $(\alpha_L,\alpha_H)\in[0,1]^2$. The four policy regions $A_1,\dots,A_4\subseteq[0,1]^2$ of Section 3.1 are defined through the infection probabilities $P^{\mathrm{inf}}$ at the pure profiles "everyone active", "only high-value agents active" and "high-value agents plus one low-value agent active", compared with the thresholds $v_L+\frac1n$ and $v_H+\frac1n$.
--
--   **Claim.** There is $M\in\mathbb N_+$ such that for every $n\ge M$,
--   $$[0,1]^2\ \subseteq\ A_1\cup A_2\cup A_3\cup A_4 .$$
--
--   The covering property is what makes Proposition 2 a complete description of symmetric equilibria. Combined with Proposition 2, it yields a symmetric equilibrium at every testing policy once $n$ is large.
--
--   **Formalization Note** The regions are the platform definitions `A1`–`A4` from `Definitions.Def_TestDistancing_Equilibrium_Model`; each requires its inequalities for every pair of a low-value agent $l$ and a high-value agent $h$.
-- source:
--   Acemoglu, Makhdoumi, Malekian & Ozdaglar, Testing, Voluntary Social Distancing and the Spread of an Infection, NBER Working Paper 27483 (July 2020), https://www.nber.org/papers/w27483, p. 12 (PDF 14): 'In the proof of Proposition 2 we show that the four sets A1, A2, A3, and A4 will cover all possible testing policies (αL, αH) ∈ [0,1]^2 (for sufficiently large n)', with footnote 2

import Mathlib
import Definitions.Def_TestDistancing_Equilibrium_Model

namespace TestDistancing.Equilibrium

/-- The four policy regions cover the policy square for all sufficiently large `n`. -/
theorem regions_cover (P : Params) (hP : P.Standing) :
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, M ≤ n → ∀ α ∈ PolicySquare,
      α ∈ A1 P n ∨ α ∈ A2 P n ∨ α ∈ A3 P n ∨ α ∈ A4 P n := by sorry

end TestDistancing.Equilibrium
