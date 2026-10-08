-- Prove2me | Theorems.Thm_SatiaLave_Bayes_bayes_return_ge_stationary_policy
-- name    : SatiaLave.Bayes.bayes_return_ge_stationary_policy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:44:56.257989+00:00
-- url     : https://prove2.me/theorems/f47f2036-5c43-4d56-90bd-a3f4d9c9f9b7
-- title:
--   Proof of Proposition 10 — f(i, g) dominates the expected return ∫[q + βP^A q + ⋯]_i dG(P) of any stationary policy
-- statement:
--   Let $f(i,g)$ be a bounded solution of the Bayesian recursive equations (10) of Satia and Lave, $g$ a prior on the unknown transition matrix $P$, $i$ a state, and $A = (A_1,\dots,A_N)$ a pure stationary policy ($A_i \in K_i$). For a matrix $P$ let $P^A$ be the $N\times N$ matrix with rows $p_i^{A_i}$ and $[q]_i = \sum_j p^{A_i}_{ij} r^{A_i}_{ij}$. Then the total expected discounted return of following $A$,
--   $$
--   V_i^A = \int \big[q + \beta P^A q + \beta^2 [P^A]^2 q + \cdots\big]_i\, dg(P),
--   $$
--   is well defined (the integrand is $g$-integrable) and
--   $$
--   f(i, g) \ge V_i^A.
--   $$
--
--   In the proof of Proposition 10 this ("Obviously, $f(i,g) \ge V_i^A$") is applied to a max-min optimal policy $A$, and the integral is then split over $P \in S$ and $P \notin S$ to obtain the lower bound.
--
--   **Formalization Note** The paper states the inequality for a max-min optimal $A$; since $f$ is the optimal Bayesian return it holds for every pure stationary policy, and that stronger form is stated. The page writes $dG(P)$ for the prior it elsewhere calls $g$, and "$p^A$" for $P^A$. The series is a componentwise `tsum`, convergent for every transition-probability matrix; integrability is part of the conclusion.
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, p. 736, Proof of Proposition 10

import Mathlib
import Definitions.Def_SatiaLave_Bayes_Model

open MeasureTheory

namespace SatiaLave.Bayes

/-- Proof of Proposition 10, p. 736: the Bayesian optimal return dominates the expected
(under the prior) total discounted return `∫ [q + β P^A q + β² [P^A]² q + ⋯]_i dg(P)` of every
pure stationary policy `A`. -/
theorem bayes_return_ge_stationary_policy {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D)
    (f : S → Measure (Mat S D) → ℝ) (hf : SolvesEq10 M f) (hb : IsBoundedOnPriors f)
    (g : Measure (Mat S D)) (hg : IsPrior g) (A : (i : S) → D i) (i : S) :
    Integrable (fun P => policyValue M A P i) g ∧
      ∫ P, policyValue M A P i ∂g ≤ f i g := by sorry

end SatiaLave.Bayes
