-- Prove2me | Theorems.Thm_TechBreakthrough_proposition_1
-- name    : TechBreakthrough.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:36:53.304632+00:00
-- url     : https://prove2.me/theorems/0b2fbb79-fd2c-48c2-bdad-3e211e571ca7
-- title:
--   Proposition 1 — $V$ is well-defined and $\bar V(x)=V(x,x)+F(x)G(x)$
-- statement:
--   Throughout, $X$ is the diffusion of §4.1 on $\mathcal I=(\alpha,\beta)$, and $R$, $G$, $f$ satisfy the standing assumptions A1–A8 of §4.2 (`Model.Valid`).
--
--   The function $V$ of problem (19) is well-defined: for all $(x,m)\in J$, every reward of (19) is integrable, and the set of expected rewards is bounded above. Moreover
--
--   $$\bar V(x)=V(x,x)+F(x)G(x),\qquad x\in\mathcal I.$$
--
--   This reduces the original problem (9), which is not Markov in $X$, to the Markovian problem for $(X,M)$.
--
--   Differences from the source:
--   - encoding: the diffusion solves (7) in law on the canonical space, with inaccessible (natural) endpoints −∞ ≤ α < β ≤ ∞ → laws P x on C(ℝ≥0, 𝓘); the Brownian motion lives on the canonical space; the Itô integral is the published step-approximation relation; natural means both integrals of Feller's test diverge; α, β are in EReal and limits at the ends are comap filters; reason: σ > 0 recovers the Brownian motion from X, and Feller's classification is what natural means; same instances
--   - reading: G is piecewise C² (undefined in the paper), and A7 holds everywhere G″ is defined → G is C² off a subset of 𝓘 with no accumulation point in 𝓘, with no condition on one-sided limits of G″; A7 at each x where deriv G is differentiable; reason: the weakest natural reading, hence the strongest theorem; every use in the paper goes through the concavity of Ĝ, which survives
--   - encoding: stopping times in T_{X,M} and expectation E_{x,m} under the law of (X, M) → stopping times in T_X under P x, with M = runningMax m a function of the path; reason: p.13: every element of T_{X,M} is P_{x,m}-a.s. in T_X, and M is a function of X and m; same values
--   - encoding: the Stieltjes integral ∫_0^τ … dM_t → the integral over (0, τ], or (0, ∞) when τ = ∞, against the Stieltjes measure of t ↦ M_{t∨0}; reason: M is continuous and nondecreasing, so the measure has no atoms; same value
--   - reading: "is well-defined" → every reward is Integrable and the set of expected rewards is BddAbove; reason: this is what the proof establishes (p.15)
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, Proposition 1, p.13

import Definitions.Def_TechBreakthrough_Model_Valid
import Definitions.Def_TechBreakthrough_Model_stopRegion

open MeasureTheory Filter
open scoped NNReal Topology

namespace TechBreakthrough

/-- Proposition 1, arXiv:2106.05112v1, p.13: the function `V` of (19) is well-defined, and
`V̄(x) = V(x, x) + F(x)G(x)`, which is (20), for all `x ∈ 𝓘`.

**Formalization Note** "Well-defined" is stated as: for all `(x, m) ∈ J`, every reward of (19) is
integrable and the set of expected rewards is bounded above. -/
theorem proposition_1 (M : Model) (hM : M.Valid) :
    (∀ z ∈ M.domain,
      (∀ τ ∈ M.T, Integrable (M.payoff z.2 τ) (M.P z.1)) ∧ BddAbove (M.valueSet z.1 z.2)) ∧
    ∀ x ∈ M.I, M.Vbar x = M.V x x + M.F x * M.G x := by sorry

end TechBreakthrough
