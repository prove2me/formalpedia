-- Prove2me | Theorems.Thm_PPDifferentiation_Costless_proposition_1
-- name    : PPDifferentiation.Costless.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:19.571094+00:00
-- url     : https://prove2.me/theorems/040d7d03-a83a-4876-9503-0ddde5748c8b
-- title:
--   Proposition 1, p. 11 — with costless PP the equilibrium positions are 1/4 and 3/4, both firms implement PP and each earns t/8
-- statement:
--   Let $t>0$ and suppose PP is costless to implement. Then:
--
--   1. $(x_A,x_B)=(1/4,3/4)$ is a position equilibrium of the game in which both firms implement PP: no firm can raise its PP/PP profit by moving to any point of $\mathbb R$;
--   2. it is the only such equilibrium with $x_A\le x_B$;
--   3. at these positions implementing PP is strictly dominant for both firms, so both firms implement PP;
--   4. the equilibrium profits are
--   $$\pi_A=\pi_B=\frac t8 .$$
--
--   The result says that costless personalized pricing pulls both firms towards the centre of the market (differentiation $1/2$ against $3/2$ without PP) and cuts each firm's profit from $3t/4$ in the uniform pricing benchmark to $t/8$.
--
--   **Formalization Note** As in the paper's proof, the stage-1 payoffs are the both-PP profits for every position pair; this reduced form rests on Lemma 1, which is posed on $x_A<x_B$, $0<x_A+x_B<2$. Deviations range over all of $\mathbb R$, including across the rival. "The firms' equilibrium positions are" is read as existence and uniqueness among ordered pairs; the mirror pair $(3/4,1/4)$ is excluded by $x_A\le x_B$.
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), p. 11, Proposition 1; proof p. 34

import Mathlib
import Definitions.Def_PPDifferentiation_Costless_Setting

namespace PPDifferentiation.Costless

theorem proposition_1 (t : ℝ) (ht : 0 < t) :
    IsPosEqPP t (1/4) (3/4) ∧
    (∀ a b : ℝ, a ≤ b → IsPosEqPP t a b → a = 1/4 ∧ b = 3/4) ∧
    PPStrictlyDominant t (1/4) (3/4) ∧
    profPP t (1/4) (3/4) = t / 8 ∧ profPP t (3/4) (1/4) = t / 8 := by sorry

end PPDifferentiation.Costless
