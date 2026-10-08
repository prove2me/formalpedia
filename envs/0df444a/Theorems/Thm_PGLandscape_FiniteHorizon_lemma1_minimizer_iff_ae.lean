-- Prove2me | Theorems.Thm_PGLandscape_FiniteHorizon_lemma1_minimizer_iff_ae
-- name    : PGLandscape.FiniteHorizon.lemma1_minimizer_iff_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:27:51.07598+00:00
-- url     : https://prove2.me/theorems/96394934-dc19-4793-937e-b054a5bff7c5
-- title:
--   Lemma 1, p. 6 (restated p. 38) — π ∈ argmin_{π′∈Π} ℓ(π′) iff J_π = J* ρ-almost surely
-- statement:
--   Let $(\mathcal S,(\mathcal A_s),g,P,\gamma,\rho)$ be a discounted Markov decision process with an optimal policy $\pi^*$, so that $J^*=J_{\pi^*}\le J_\pi$ pointwise for every feasible policy $\pi$, and let $\ell(\pi)=(1-\gamma)\int J_\pi\,d\rho$. Then for every feasible measurable stationary policy $\pi\in\Pi$,
--   $$\pi\in\arg\min_{\pi'\in\Pi}\ell(\pi')\iff J_\pi=J^*\ \ \rho\text{-almost surely, i.e. }\rho(\{s\in\mathcal S:J_\pi(s)=J^*(s)\})=1 .$$
--
--   The lemma links minimizers of the policy gradient loss to optimal policies in the dynamic-programming sense: minimizing the average cost under $\rho$ identifies the optimal cost-to-go on the support of $\rho$.
--
--   **Formalization Note** $J^*$ is $J_{\pi^*}$ for an optimal policy $\pi^*$ (the page asserts existence under Assumption 2); Assumptions 1 and 2 are not needed for this statement and are dropped, which makes it stronger. "$\arg\min_{\pi'\in\Pi}$" is: $\ell(\pi)\le\ell(\pi')$ for every feasible measurable stationary $\pi'$.
-- source:
--   arXiv:1906.01786v3, Lemma 1, p. 6 (restated with proof, App. D.1, p. 38)

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

namespace PGLandscape.FiniteHorizon

open MeasureTheory ProbabilityTheory

/-- Lemma 1, arXiv:1906.01786v3, p. 6 (proof p. 38): a policy `π ∈ Π` minimizes `ℓ` over `Π` if and
only if `J_π = J*` `ρ`-almost surely, where `J* = J_{π*}` for an optimal policy `π*`. -/
theorem lemma1_minimizer_iff_ae {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : PGLandscape.Closure.MDP S A) (πstar : PGLandscape.Closure.MPolicy S A) (hopt : PGLandscape.Closure.IsOptimal M πstar)
    (π : PGLandscape.Closure.MPolicy S A) (hπ : PGLandscape.Closure.IsFeasible M π) :
    (∀ π' : PGLandscape.Closure.MPolicy S A, PGLandscape.Closure.IsFeasible M π' → PGLandscape.Closure.loss M π ≤ PGLandscape.Closure.loss M π') ↔
      ∀ᵐ s ∂M.ρ, PGLandscape.Closure.costToGo M π s = PGLandscape.Closure.costToGo M πstar s := by sorry

end PGLandscape.FiniteHorizon
