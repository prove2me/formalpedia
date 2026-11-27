-- Prove2me | Theorems.Thm_SocialManip_Beliefs_Supplement_proposition_2
-- name    : SocialManip.Beliefs.Supplement.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T04:14:32.330231+00:00
-- url     : https://prove2.me/theorems/09a65529-95db-4d7c-a1cf-38a30b31e3a1
-- title:
--   Proposition 2, p. 14 — the DeGroot centrality D(γ) is finite, equals (I − W)⁻¹(γ ⊙ θ), and is the a.s. limiting belief of the incorrect state
-- statement:
--   Let an admissible finite network satisfy Assumption 1 and the standing game constraints. Fix the realized state $y$, a false message $\hat y\ne y$, and a targeting vector $x\in\{0,1\}^n$. Write $\gamma_i=0$ on the Bayesian set $B$ and $\gamma_i=x_i$ otherwise. Define $D_i(\gamma)$ by the sum of the weights of all finite Bayesian-avoiding walks, including length zero, weighted by $\theta_j\gamma_j$ at the endpoint. Then every $D_i(\gamma)$ is finite and
--   $$D(\gamma)=(I-W)^{-1}(\gamma\odot\theta),\qquad \pi_T(\hat y)\longrightarrow D(\gamma)\quad\text{almost surely as }T\to\infty.$$
--   The walk definition is independent of the inverse-matrix formula; this result identifies the two and relates them to the actual physical-time belief path.
--
--   **Formalization Note** Poisson arrivals use a common organic clock and a common independent principal clock. Only targeted agents receive the latter stream. The social exchange interval is one. Nonnegative walk sums take values in $[0,\infty]$ before the theorem establishes finiteness.
--
--   Differences from the source:
--   - reading: influence vector of §3.2 → a fixed false message and targeting vector, with zero Bayesian influence; reason: this is the intervention defining γ on p. 12
--   - encoding: real nonnegative walk sums → extended nonnegative sums plus an explicit finiteness conclusion; reason: divergence cannot become a totalized real value zero
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), Proposition 2, p. 14; Definition 4 and walks p. 13; (2) p. 12; proof pp. 47–48

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game

open MeasureTheory ProbabilityTheory Filter Topology Matrix

namespace SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

theorem proposition_2 {n : ℕ} (M : Model n) (hS : M.Standing) (hG : M.GameDomain)
    (adj : Fin n → Fin n → Prop) (hA : M.Assumption1 adj)
    (y yhat : State) (hyhat : yhat ≠ y) (x : Fin n → Bool) :
    (∀ i, centrality M.B M.θ M.α (influence M.B x) i ≠ ⊤) ∧
      (fun i => (centrality M.B M.θ M.α (influence M.B x) i).toReal) =
        (1 - W M.B M.α)⁻¹ *ᵥ (fun i => influence M.B x i * thetaVec M.B M.θ i) ∧
      ∀ᵐ ω ∂(sampleMeasure M y),
        Tendsto (fun T : ℝ => fun i =>
          if yhat = State.R then beliefR M y yhat x ω T i
          else 1 - beliefR M y yhat x ω T i) atTop
          (𝓝 fun i => (centrality M.B M.θ M.α (influence M.B x) i).toReal) := by sorry

end SocialManip.Beliefs.Supplement
