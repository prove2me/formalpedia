-- Prove2me | Theorems.Thm_SocialManip_Beliefs_Supplement_proposition_11
-- name    : SocialManip.Beliefs.Supplement.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:16:39.716274+00:00
-- url     : https://prove2.me/theorems/90ddb60a-9719-4123-bd77-bb11bd7ea1b9
-- title:
--   Proposition 11, p. 36 (corrected: refutation) — no universal Bayesian threshold even at δ = 0
-- statement:
--   The proposed universal Bayesian threshold fails under the density convention supported by the paper's examples (DeGroot starting vertices; a terminal vertex may be Bayesian). Fix $q=1/2$, $\lambda=\lambda^*=1$, $\varepsilon=1/4$, $b=0$ and $\delta=0$. For every proposed threshold $m^*$ there is a finite network, satisfying the standing constraints, the game domain and Assumption 1, with a nonempty Bayesian set of size at least $m^*$ and a locally dense cover consisting of the entire network, which is susceptible:
--   $$\forall m^*\in\mathbb N,\quad\exists G:\quad |B|\ge m^*,\qquad G\text{ is 0-dense},\qquad\neg\operatorname{Impervious}(G).$$
--   The locally dense cover, where used, has the single set $I_1=\{1,\ldots,n\}$. This states a refutation of the printed universal-threshold claim, rather than a weakened positive theorem. DISPROOF.md gives an exact hub–chain–leaf family, its path weights, and its centralities.
--
--   **Formalization Note** The density domain is an explicit source correction. The literal maximum on p. 19 includes Bayesian starts, whose rows of $W$ are zero; the finite-diameter examples on p. 37 instead require DeGroot starts and allow Bayesian terminal vertices. The refutation uses that non-vacuous convention, with every allowed positive weight retained. It does not refute the vacuous literal all-start interpretation. The belief and payoff path uses genuine physical-time Poisson counts and unit-time social exchanges.
--
--   Differences from the source:
--   - correction: Proposition 11 asserts a universal Bayesian threshold for density → refutation at fixed q=1/2, lam=lamStar=1, ε=1/4, b=δ=0, with arbitrarily many Bayesians; reason: exact family has minimum centrality (2n+50)/(2n+25m+50) tending to 1; printed proof double-counts concatenated walks
--   - reading: log-diameter over all starts using zero Bayesian rows → DeGroot starts, terminal Bayesian allowed; reason: the finite-diameter examples on p. 37 require this non-vacuous convention; zero Bayesian rows cannot reach another vertex, so the correction explicitly excludes Bayesian starts
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), Proposition 11 and Definition 9, p. 36; proof pp. 56–57

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game

namespace SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

/-- The same counterexample to the universal threshold already has a locally dense cover
consisting of the whole network, so it refutes the local version as well. -/
theorem proposition_11 :
    ∀ mstar : ℕ, ∃ (n : ℕ) (M : Model n) (adj : Fin n → Fin n → Prop),
      M.Standing ∧ M.GameDomain ∧ M.q = 1 / 2 ∧ M.lam = 1 ∧ M.lamStar = 1 ∧
        M.ε = 1 / 4 ∧ M.b = 0 ∧ M.Assumption1 adj ∧
        IsLocallyDenseCover M.B M.α 0 1 (fun _ => Finset.univ) ∧
        0 < M.B.card ∧ mstar ≤ M.B.card ∧ ¬ Impervious M := by sorry

end SocialManip.Beliefs.Supplement
