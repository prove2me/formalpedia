-- Prove2me | Theorems.Thm_SocialManip_Beliefs_Supplement_lemma_2
-- name    : SocialManip.Beliefs.Supplement.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:19:57.813254+00:00
-- url     : https://prove2.me/theorems/9d945fdb-91a4-4158-81b3-726c6fe6abf7
-- title:
--   Lemma 2, p. 43 (corrected: refutation) — fresh two-hop private news prevents contemporaneous reconstruction
-- statement:
--   The contemporaneous reconstruction in printed Lemma 2(b) fails before information crosses the first social-exchange boundary. There are three agents: Bayesian $0$ observes only DeGroot $1$, and both DeGroots $1,2$ have positive social weights on all three agents. Set $\Delta=1$, $q=\mu_0=1/2$, true organic rates $\lambda_i=1$, lower rate bound $9/10$, upper principal capacity $2$, and signal qualities $p_i=4/5$. The standing constraints and Assumption 2(a)–(e) hold. Failure persists outside any proposed Lebesgue-null exceptional set of the DeGroot rows: some weights outside that set satisfy these constraints and make $\pi_{2,1/2}$ unrecoverable from Bayesian $0$'s observations at time $1/2$, even with a pure non-interfering principal.
--   $$\nexists\, g\text{ measurable}:\quad \pi_{2,1/2}=g(\text{observations of agent }0\text{ at }1/2)\quad\text{almost surely}.$$
--   This refutes the printed lemma, without asserting an unverified delayed-history replacement. DISPROOF.md records the independent-news argument and the open set of permissible weights.
--
--   **Formalization Note** Genericity uses the free DeGroot-row coordinates, as elsewhere in this draft. The witness includes a valid causal reporting mechanism with full continuous neighbourhood histories. Bayesian $0$ has no Bayesian neighbour. Before the first exchange, her observations still contain only her own news and DeGroot $1$'s news-driven path. There is no assumption that a reporting mechanism already exists, and no restriction to grid reports.
--
--   Differences from the source:
--   - correction: Lemma 2 asserts reconstruction for every time and every reachable agent → a three-agent refutation of contemporaneous clause (b), persisting outside every Lebesgue-null exceptional set; reason: on $(0,\Delta)$ private news of the second-hop DeGroot has not entered any observation of the Bayesian, yet changes the DeGroot's current belief.
--   - reading: genericity in the printed ambient space of weights → genericity in the free DeGroot rows of the social matrix; reason: row normalization determines the experience weights, so the redundant ambient coordinates carry no smooth probability distribution on the constraint set.
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), Lemma 2, p. 43; proof pp. 44–45; Assumption 2 p. 34

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game
import Definitions.Def_SocialManip_Beliefs_Supplement_AppendixA

open MeasureTheory

namespace SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

/-- Refutation of the contemporaneous reconstruction in printed Lemma 2(b). Bayesian 0 sees
DeGroot 1, who sees DeGroot 2 only through the lagged social update. Before the first exchange,
agent 2's private news cannot enter agent 0's observations. Failure occurs on an open set of
positive DeGroot rows, so no Lebesgue-null generic exception can remove it. -/
theorem lemma_2 :
    ∀ Z : Set ({i : Fin 3 // i ∉ ({0} : Finset (Fin 3))} → Fin 3 → ℝ), volume Z = 0 →
      ∃ M : AModel 3, M.Standing ∧ M.Assumption2 ∧ M.B = {0} ∧ M.N 0 = {1} ∧
        M.Δ = 1 ∧ M.q = 1 / 2 ∧ M.μ0 = 1 / 2 ∧
        M.lamLow = 9 / 10 ∧ M.lamUp = 2 ∧ (∀ i, M.lam i = 1) ∧
        (∀ i, M.p i = 4 / 5) ∧ (∀ i ∉ M.B, ∀ j, 0 < M.α i j) ∧
        degrootRows ({0} : Finset (Fin 3)) M.α ∉ Z ∧
        let σP : APrincipalStrategy 3 := fun _ => Measure.dirac (truthfulAction 3)
        ∃ R : AReporting 3, AValidReporting M (1 / 2) σP R ∧
          ¬ ∃ g : LocalHistory 3 (1 / 2) → ℝ,
            Measurable g ∧ ∀ᵐ z ∂(trueLaw M State.S false (truthfulAction 3)),
              beliefA M R (1 / 2) 2 z =
                g (obsWith M R (1 / 2) 0 z) := by sorry

end SocialManip.Beliefs.Supplement
