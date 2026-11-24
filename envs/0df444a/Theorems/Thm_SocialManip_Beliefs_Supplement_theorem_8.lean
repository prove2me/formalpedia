-- Prove2me | Theorems.Thm_SocialManip_Beliefs_Supplement_theorem_8
-- name    : SocialManip.Beliefs.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:20:49.128575+00:00
-- url     : https://prove2.me/theorems/04a6fe8c-1fb3-4782-a019-737f6bea3685
-- title:
--   Theorem 8, p. 35 (corrected: domain refutation) — Assumption 2 permits no Bayesians
-- statement:
--   Assumption 2 does not require any Bayesian agent. Its pure false-interference branch of (*) nevertheless requires detection by some Bayesian. For every Lebesgue-null exceptional set of normalized two-agent DeGroot rows, there is a model outside that set with $B=\varnothing$, strictly positive social and personal weights, signal qualities $4/5$, true rates $1$, lower rate bound $9/10$, capacity $2$, and priors $q=\mu_0=1/2$, satisfying the standing constraints and Assumption 2(a)–(e). An admissible nonzero action with false message R in state S exists, while
--   $$\nexists i\in B.$$
--   Every such action can be played as a pure principal strategy, so the existential Bayesian conclusion of (*) is false. The normalized positive rows form an open set; no Lebesgue-null generic exception repairs the missing Bayesian set.
--
--   This is a domain refutation of the entire printed conjunction through one false clause. It does not refute each other branch separately, does not replace almost-sure learning by convergence in probability, and does not claim a positive learning theorem for nonempty Bayesian networks. No posterior-version choice or history approximation enters the counterexample.
--
--   Differences from the source:
--   - correction: Assumption 2 implies all branches of (*) and almost-sure absence of Bayesian manipulation → a generic admissible empty-Bayesian instance falsifies the existential Bayesian clause; reason: all numerical, connectivity and positivity assumptions hold simultaneously on an open set, yet there is no possible Bayesian witness
--   - reading: generic weights in the printed redundant ambient dimension → Lebesgue genericity in normalized free social rows; reason: row normalization fixes θ; an ambient density on the larger row-sum hyperplane would make the model inconsistent
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), Theorem 8 and properties (*), p. 35; Assumption 2 p. 34; proof pp. 54–56

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game
import Definitions.Def_SocialManip_Beliefs_Supplement_AppendixA

open MeasureTheory Filter Topology

namespace SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

/-- The printed Assumption 2 permits no Bayesian agents. Its pure-interference branch of (*)
then asks for a member of the empty set. Positive normalized rows on an open set satisfy all
other assumptions, so an exceptional Lebesgue-null set cannot repair the omitted domain. -/
theorem theorem_8 :
    ∀ Z : Set ({i : Fin 2 // i ∉ (∅ : Finset (Fin 2))} → Fin 2 → ℝ), volume Z = 0 →
      ∃ M : AModel 2, M.Standing ∧ M.Assumption2 ∧ M.B = ∅ ∧
        M.q = 1 / 2 ∧ M.μ0 = 1 / 2 ∧ M.lamLow = 9 / 10 ∧ M.lamUp = 2 ∧
        (∀ i, M.lam i = 1) ∧ (∀ i, M.p i = 4 / 5) ∧
        (∀ i j, 0 < M.α i j) ∧ (∀ i, 0 < M.θ i) ∧
        degrootRows (∅ : Finset (Fin 2)) M.α ∉ Z ∧
        ∃ a : AAction 2, a.Admissible M ∧ a.1 ≠ State.S ∧ (∃ i, a.2.1 i = true) ∧
          ¬ ∃ i : Fin 2, i ∈ M.B := by sorry

end SocialManip.Beliefs.Supplement
