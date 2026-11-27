-- Prove2me | Theorems.Thm_SocialManip_Beliefs_Supplement_proposition_1
-- name    : SocialManip.Beliefs.Supplement.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T04:13:45.232025+00:00
-- url     : https://prove2.me/theorems/af7988a4-f32d-4628-a99d-334c5b70d683
-- title:
--   Proposition 1, p. 11 — under Assumption 1, with a truthful principal every agent's belief in the true state tends to 1 almost surely
-- statement:
--   Let $B$ be the Bayesian set in an admissible finite network with signal qualities $p_i\in[1/2,1)$, prior $q\in(0,1)$, positive news rates, and Assumption 1. Fix the realized state $y\in\{S,R\}$. The truthful principal sends no messages. Organic news arrives at the common Poisson clock of rate $\lambda$, with contents independent across agents and arrivals. Bayesians hold the truth; DeGroots start from the prior and exchange beliefs at unit intervals. Then
--   $$\pi_T(R)\longrightarrow\mathbf1_{\{y=R\}}\mathbf1\quad\text{almost surely as physical time }T\to\infty.$$
--   Every agent therefore learns the true state without interference. This supplies the truthful counterfactual used in manipulation comparisons.
--
--   **Formalization Note** Between exchanges personal experience uses the current finite Poisson history and the social term uses the preceding exchange, as specified in Appendix A with $\Delta=1$. The state and belief formula are reused from the immutable published setting; the physical-time path is defined locally.
--
--   Differences from the source:
--   - reading: main-text recursion specified at integer social exchanges → continuous-time news counts with the between-exchange convention of Appendix A, p. 33; reason: at every integer exchange this is the p. 7 recursion; no deterministic message-count substitution is made
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), Proposition 1, p. 11; proof p. 47

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game

open MeasureTheory ProbabilityTheory Filter Topology

namespace SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

theorem proposition_1 {n : ℕ} (M : Model n) (hS : M.Standing) (hG : M.GameDomain)
    (adj : Fin n → Fin n → Prop) (hA : M.Assumption1 adj) (y : State) :
    ∀ᵐ ω ∂(sampleMeasure M y),
      Tendsto (fun T : ℝ => beliefR M y y (fun _ => false) ω T) atTop
        (𝓝 fun _ => truth y State.R) := by sorry

end SocialManip.Beliefs.Supplement
