-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_Supplement_osrc_bound
-- name    : RankCutFacility.Shifted.Supplement.osrc_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:25:18.9619+00:00
-- url     : https://prove2.me/theorems/d6b6d575-7dc6-43ba-83ef-f9977cd8dff8
-- title:
--   Theorem A.1 — Order-statistic-clock bound and $\rho^*_R<3.402$
-- statement:
--   Let OSRC$_\mu$ sample $n$ independent Uniform$(0,1)$ clocks independently of the arrival order, sort them $Z_{(1)}\le\dots\le Z_{(n)}$, and give the request at rank $t$ the penalty $\lambda_t=\min\{1,Z_{(t)}/\mu\}$, using the candidate choice and opening test of Algorithm 1 with the fixed tie order. Fix any metric space, candidate geometry with positive costs, horizon $n\ge1$ and demand copies, and an optimal solution with opening cost $F^*$ and connection cost $R^*$.
--
--   **Theorem A.1.** For every $\mu\in(0,1]$, the cost of every run is integrable in the clocks and
--
--   $$\mathbb E[\mathrm{ALG}]\le A(\mu)F^*+(3+3\mu)R^*,\qquad A(\mu)=1+\frac{e^{-(1+\mu)}}{\mu}.\tag{41}$$
--
--   Let $\mu_R$ be the unique solution in $(0,1]$ of $e^{-(1+\mu_R)}=\mu_R(2+3\mu_R)$ and $\rho^*_R=A(\mu_R)=3+3\mu_R$ (42). This parameter minimizes the bound $\max\{A(\mu),3+3\mu\}$ over $\mu\in(0,1]$, and $\rho^*_R<3.402$.
--
--   Randomizing only the rank clock thus improves the deterministic constant $3.538$ within the same penalized-distance architecture.
--
--   Differences from the source:
--   - encoding: E over the clocks of the run cost → Bochner integral against the product of Lebesgue measure on [0,1], with integrability of every run cost as a conclusion; reason: the conclusion excludes the zero default of a non-integrable integrand; the closed interval differs from (0,1) by a null set
--   - encoding: sorted clocks Z_(1) < … < Z_(n) → the t-th entry of the sorted list of clock values; reason: ties among the clocks have probability zero
--   - encoding: a fixed optimal solution and its clusters → Comparator together with IsOptimal (optimal, nearest assignment, no unused facility) and cluster Q c; reason: this is the published encoding of the standing assumptions of the cluster analysis
--   - encoding: µ_R, the unique solution in (0,1] of e^{-(1+µ)} = µ(2+3µ) → the canonical sInf of the solution set in (0,1], with existence, uniqueness and the equation as conclusions; reason: the conclusions exclude the default value of an empty or degenerate solution set without adding a hypothesis
--   - encoding: this parameter minimizes the bound → max{A(µ_R), 3+3µ_R} ≤ max{A(µ), 3+3µ} for every µ ∈ (0,1]; reason: the bound of (41) as a ratio is max{A(µ), 3+3µ}
--   - encoding: a finite nonempty candidate set with a fixed total order in an arbitrary metric space, positive costs → the published Geometry: an injective enumeration Fin m → M with m > 0 and positive real fees; reason: every finite ordered candidate set has such an enumeration; no condition is imposed on the ambient metric
--   - encoding: a multiset of n demand copies → a map u : Fin n → M (repeated locations allowed); reason: labels distinguish repeated copies for permutation ranks and never enter an online decision
--   - encoding: expectation over the uniformly random arrival order → finite average over all n! permutations of the labeled copies; reason: this is exactly the finite uniform law; no measurability assumption is needed
--   - encoding: every horizon n, including n = 0 (empty multiset, ALG = OPT = 0) → the upper-bound clauses assume 0 < n; reason: at n = 0 the source's bound reads 0 ≤ 0, while the published optimum minimizes over nonempty facility sets; the hypothesis excludes only this degenerate horizon
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Theorem A.1, eqs. (41)–(42), printed p. 27 (PDF p. 29)

import Definitions.Def_RankCutFacility_Shifted_Supplement_Runs

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace RankCutFacility.Shifted.Supplement
open RankCutFacility.Shifted

/-- Theorem A.1 (PDF p. 29, printed p. 27). (41) for OSRC_µ against any optimal solution
(with integrability of every run cost in the clocks), and (42): `µ_R` is the unique root in
`(0,1]`, `ρ*_R = A(µ_R) = 3 + 3µ_R` minimizes `max{A(µ), 3 + 3µ}` over `(0,1]`, and
`ρ*_R < 3.402`. -/
theorem osrc_bound :
    (∀ {M : Type*} [MetricSpace M] (G : Geometry M) {n : ℕ}, 0 < n → ∀ (u : Fin n → M) (μ : ℝ),
      0 < μ → μ ≤ 1 → ∀ (Q : Comparator G n), IsOptimal G u Q →
        (∀ π : Arrival n, Integrable (fun z => osrcRun G u μ z π) (clockLaw n)) ∧
        osrcExpected G u μ ≤
          limitingA μ * openingCost G Q.opened + (3 + 3 * μ) * connectionCost G u Q.opened) ∧
    (0 < muR ∧ muR ≤ 1 ∧ Real.exp (-(1 + muR)) = muR * (2 + 3 * muR) ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ 1 → Real.exp (-(1 + μ)) = μ * (2 + 3 * μ) → μ = muR) ∧
    rhoR = limitingA muR ∧ rhoR = 3 + 3 * muR ∧
    (∀ μ : ℝ, 0 < μ → μ ≤ 1 → max (limitingA muR) (3 + 3 * muR) ≤ max (limitingA μ) (3 + 3 * μ)) ∧
    rhoR < (3402 / 1000 : ℝ) := by sorry

end RankCutFacility.Shifted.Supplement
