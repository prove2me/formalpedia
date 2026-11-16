-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_Supplement_osrc_tight
-- name    : RankCutFacility.Shifted.Supplement.osrc_tight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:25:51.463094+00:00
-- url     : https://prove2.me/theorems/b337077a-41ae-46a2-a6ce-d960fbdd1b76
-- title:
--   Theorem A.2 — Tightness: $\mathrm{CR}_R(\mu)=\max\{A(\mu),3+3\mu\}$
-- statement:
--   Let $\mathrm{CR}_R(\mu)$ be the worst-case expected competitive ratio of OSRC$_\mu$ (Theorem A.1), the supremum of $\mathbb E[\mathrm{ALG}]/\mathrm{OPT}$ over finite instances and horizons.
--
--   **Theorem A.2.** For every fixed $\mu\in(0,1]$,
--
--   $$\mathrm{CR}_R(\mu)=\max\{A(\mu),3+3\mu\}.$$
--
--   That is: on every instance (any metric, positive costs, $n\ge1$, any tie order) the run costs are integrable and $\mathbb E[\mathrm{ALG}]\le\max\{A(\mu),3+3\mu\}\,\mathrm{OPT}$; and for every $c<\max\{A(\mu),3+3\mu\}$ there is a finite instance (finite metric, finite nonempty candidate set with positive costs, $n\ge1$ demand copies) on which $\mathbb E[\mathrm{ALG}]>c\cdot\mathrm{OPT}$ under every candidate tie order. In particular the best parameter of the family is $\mu_R$, the unique root in $(0,1]$ of $e^{-(1+\mu)}=\mu(2+3\mu)$, with ratio $\rho^*_R=\max\{A(\mu_R),3+3\mu_R\}$.
--
--   Both coefficients of (41) are therefore necessary for this rule.
--
--   Differences from the source:
--   - encoding: CR_R(µ) = max{A(µ), 3+3µ} as a supremum identity → the upper bound on every instance together with, for every smaller c, a finite instance exceeding c · OPT; reason: a supremum equals a value exactly when it bounds every element and every smaller value is exceeded
--   - generalization: a bad finite instance for the rule with its fixed tie order → a finite instance on which E[ALG] > c · OPT under every candidate enumeration; reason: a bad instance for every tie order is in particular bad for the rule's own
--   - encoding: E over the clocks of the run cost → Bochner integral against the product of Lebesgue measure on [0,1], with integrability of every run cost as a conclusion; reason: the conclusion excludes the zero default of a non-integrable integrand
--   - encoding: µ_R, the unique solution in (0,1] of e^{-(1+µ)} = µ(2+3µ) → the canonical sInf of the solution set in (0,1], with existence, uniqueness and the equation as conclusions; reason: the conclusions exclude the default value of an empty or degenerate solution set without adding a hypothesis
--   - encoding: a finite nonempty candidate set with a fixed total order in an arbitrary metric space, positive costs → the published Geometry: an injective enumeration Fin m → M with m > 0 and positive real fees; reason: every finite ordered candidate set has such an enumeration; no condition is imposed on the ambient metric
--   - encoding: a multiset of n demand copies → a map u : Fin n → M (repeated locations allowed); reason: labels distinguish repeated copies for permutation ranks and never enter an online decision
--   - encoding: expectation over the uniformly random arrival order → finite average over all n! permutations of the labeled copies; reason: this is exactly the finite uniform law; no measurability assumption is needed
--   - encoding: every horizon n, including n = 0 (empty multiset, ALG = OPT = 0) → the upper-bound clauses assume 0 < n; reason: at n = 0 the source's bound reads 0 ≤ 0, while the published optimum minimizes over nonempty facility sets; the hypothesis excludes only this degenerate horizon
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Theorem A.2, printed p. 29 (PDF p. 31)

import Definitions.Def_RankCutFacility_Shifted_Supplement_Runs

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace RankCutFacility.Shifted.Supplement
open RankCutFacility.Shifted

/-- Theorem A.2 (PDF p. 31, printed p. 29). For every `µ ∈ (0,1]` the worst-case expected ratio
of OSRC_µ is exactly `max{A(µ), 3 + 3µ}`: the bound holds on every instance, and every smaller
`c` is exceeded on some finite instance under every candidate tie order. In particular the best
parameter of the family, `µ_R`, has ratio `ρ*_R`. -/
theorem osrc_tight :
    (∀ μ : ℝ, 0 < μ → μ ≤ 1 →
      (∀ {M : Type*} [MetricSpace M] (G : Geometry M) {n : ℕ}, 0 < n → ∀ u : Fin n → M,
        (∀ π : Arrival n, Integrable (fun z => osrcRun G u μ z π) (clockLaw n)) ∧
        osrcExpected G u μ ≤ max (limitingA μ) (3 + 3 * μ) * optimum G u) ∧
      (∀ c : ℝ, c < max (limitingA μ) (3 + 3 * μ) →
        ∃ (X : Type) (_ : MetricSpace X) (_ : Finite X) (S : Set X) (f : X → ℝ),
          S.Nonempty ∧ (∀ x ∈ S, 0 < f x) ∧ ∃ n : ℕ, 0 < n ∧ ∃ u : Fin n → X,
            ∀ G : Geometry X, Set.range G.site = S → (∀ y, G.fee y = f (G.site y)) →
              c * optimum G u < osrcExpected G u μ)) ∧
    (0 < muR ∧ muR ≤ 1 ∧ Real.exp (-(1 + muR)) = muR * (2 + 3 * muR) ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ 1 → Real.exp (-(1 + μ)) = μ * (2 + 3 * μ) → μ = muR) ∧
    max (limitingA muR) (3 + 3 * muR) = rhoR ∧
    (∀ μ : ℝ, 0 < μ → μ ≤ 1 → rhoR ≤ max (limitingA μ) (3 + 3 * μ)) := by sorry

end RankCutFacility.Shifted.Supplement
