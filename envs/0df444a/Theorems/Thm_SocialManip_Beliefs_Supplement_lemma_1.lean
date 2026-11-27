-- Prove2me | Theorems.Thm_SocialManip_Beliefs_Supplement_lemma_1
-- name    : SocialManip.Beliefs.Supplement.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T04:19:14.945408+00:00
-- url     : https://prove2.me/theorems/a5649fe9-c35d-4c9a-bb14-23d60982a8ce
-- title:
--   Lemma 1, p. 43 (corrected: refutation) — finite-horizon interference in state R
-- statement:
--   Lemma 1 asserts no interference in state R in every equilibrium, although its proof only argues as the horizon tends to infinity. The finite-horizon assertion is false even with the substantive rate and generic-weight conditions of Assumption 2. Outside every proposed null set of normalized two-agent DeGroot weight rows, there is an all-DeGroot network with all social and personal weights positive, $p_i=4/5$, true rates $1$, lower rate bound $9/10$, capacity $2$, priors $q=\mu_0=1/2$, sharing interval $\Delta=1$, cost $\varepsilon=1/10$, and $b=0$, satisfying all standing constraints and Assumption 2(a)–(e), for which
--   $$\exists\sigma:\quad\sigma\text{ is an equilibrium at }T=1/2,\qquad
--   \mathbb P_\sigma(x\ne0\mid y=R)=1.$$
--   Before the first exchange, adding R signals strictly increases the chance of action R in either state. Sending R at maximal rate to both agents is optimal with the chosen small positive cost. Positive normalized rows form an open set, so genericity cannot eliminate the examples.
--
--   This refutes the printed every-equilibrium claim. It does not assert a corrected asymptotic claim or use an unexplained large-horizon premise. The witness includes a valid causal reporting mechanism. With no Bayesians, its reporting equations are exactly the DeGroot recursion; no Bayesian posterior is supplied as a hypothesis.
--
--   Differences from the source:
--   - correction: every equilibrium has x=0 in state R → generic finite-horizon equilibria with interference probability one in state R; reason: the proof substitutes eventual truthful learning for finite-time correct action; positive-rate R news has a strictly profitable finite-time effect
--   - reading: smooth weights in a redundant ambient dimension → Lebesgue genericity in normalized free social rows; reason: θ is determined by row sums; the counterexample holds on an open set of those coordinates
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), Lemma 1, p. 43 and its proof

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game
import Definitions.Def_SocialManip_Beliefs_Supplement_AppendixA

open MeasureTheory

namespace SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

/-- A generic all-DeGroot finite-horizon counterexample to the printed “every equilibrium”
claim. Before the first social exchange a positive-rate R stream strictly improves the chance
of action R in state R. With small positive cost the principal targets both agents. -/
theorem lemma_1 :
    ∀ Z : Set ({i : Fin 2 // i ∉ (∅ : Finset (Fin 2))} → Fin 2 → ℝ), volume Z = 0 →
      ∃ M : AModel 2, M.Standing ∧ M.Assumption2 ∧ M.B = ∅ ∧
        M.Δ = 1 ∧ M.ε = 1 / 10 ∧ M.b = 0 ∧ M.q = 1 / 2 ∧ M.μ0 = 1 / 2 ∧
        M.lamLow = 9 / 10 ∧ M.lamUp = 2 ∧
        (∀ i, M.lam i = 1) ∧ (∀ i, M.p i = 4 / 5) ∧
        (∀ i j, 0 < M.α i j) ∧ (∀ i, 0 < M.θ i) ∧
        degrootRows (∅ : Finset (Fin 2)) M.α ∉ Z ∧
        ∃ (σP : APrincipalStrategy 2) (R : AReporting 2) (σA : AAgentStrategy 2),
          AIsEquilibrium M (1 / 2) σP R σA ∧
            σP State.R {a | ∃ i, a.2.1 i = true} = 1 := by sorry

end SocialManip.Beliefs.Supplement
