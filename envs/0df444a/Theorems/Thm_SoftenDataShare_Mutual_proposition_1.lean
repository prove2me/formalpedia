-- Prove2me | Theorems.Thm_SoftenDataShare_Mutual_proposition_1
-- name    : SoftenDataShare.Mutual.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:12:58.4774+00:00
-- url     : https://prove2.me/theorems/31ad6101-a213-4f0d-b649-b403745764e7
-- title:
--   Proposition 1 — for every MHR distribution, sharing data on [z^N, b′] satisfies firm 2's (IC) and makes both firms strictly better off
-- statement:
--   Consumers are distributed on the Hotelling line $[0,1]$ according to a monotone-hazard-rate distribution $(F,f)$ (positive continuous density, strictly increasing hazard rate $h=f/(1-F)$). Firm 1 at $0$ knows every consumer's location; firm 2 at $1$ knows none. Let $z^N$ be the benchmark marginal consumer of Eq. (1), $z^N=1/2+1/h(z^N)$, and let $\pi^N_1,\pi^N_2$ be the benchmark profits of Eq. (2). For data sharing on $[a,b]$, let $\pi_1(a,b)$, $\pi_2(a,b)$ be the profits of Eqs. (8) and (7) when firm 2's uniform price serves only $[b,1]$, and let $\pi_{21}(b)=(2b-1)(1-F(b))$ and $\pi_{22}(a,b)$ be firm 2's best profits from its two uniform-pricing options (Eqs. (4)–(5)).
--
--   Then:
--   1. for every $b$ with $z^N<b\le1$,
--   $$\pi_1(z^N,b)>\pi^N_1\qquad\text{and}\qquad\pi_2(z^N,b)>\pi^N_2;$$
--   2. there is $b'\in(z^N,1)$ such that firm 2 strictly prefers to serve only $[b',1]$ with its uniform price,
--   $$\pi_{21}(b')>\pi_{22}(z^N,b'),$$
--   so firm 2's incentive constraint (IC) holds for sharing on $[z^N,b']$, and at that $b'$ both firms are strictly better off than without data sharing: $\pi_1(z^N,b')>\pi^N_1$ and $\pi_2(z^N,b')>\pi^N_2$.
--
--   This is the paper's central result: a fully informed firm can gain by giving customer data to its uninformed rival, because sharing data on the rival's own customer base $[z^N,b']$ while keeping $[b',1]$ private induces the rival to raise its uniform price, which softens competition for every consumer firm 1 keeps.
--
--   **Formalization Note** $z^N$ enters as a number satisfying Eq. (1) (`IsZN`); its existence and uniqueness is a separate theorem. $\pi_{22}$ is defined as a maximum over $z'\in[0,a]$, not through the first-order condition (5). Part 2 is strict, as in the paper's proof; part 1 includes $b=1$.
-- source:
--   Choe, Cong & Wang, Softening Competition through Unilateral Sharing of Customer Data, Monash Discussion Paper 2021-10 (rev. Oct. 20, 2022), pp. 11–12, Proposition 1; proof pp. 34–36

import Mathlib
import Definitions.Def_SoftenDataShare_Mutual_MHRDist
import Definitions.Def_SoftenDataShare_Mutual_Model

namespace SoftenDataShare.Mutual

theorem proposition_1 {F f : ℝ → ℝ} {zN : ℝ} (hF : MHRDist F f)
    (hzN : IsZN F f zN) :
    (∀ b : ℝ, zN < b → b ≤ 1 →
        piN1 F f zN < pi1 f zN b ∧ piN2 F f zN < pi2 F f zN b) ∧
      ∃ b' ∈ Set.Ioo zN 1, pi22 F zN b' < pi21 F b' ∧
        piN1 F f zN < pi1 f zN b' ∧ piN2 F f zN < pi2 F f zN b' := by sorry

end SoftenDataShare.Mutual
