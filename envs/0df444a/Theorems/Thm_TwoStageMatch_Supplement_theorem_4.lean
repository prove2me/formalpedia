-- Prove2me | Theorems.Thm_TwoStageMatch_Supplement_theorem_4
-- name    : TwoStageMatch.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:14:08.115077+00:00
-- url     : https://prove2.me/theorems/cb314350-8478-5568-b8f0-5bd5ea20c887
-- title:
--   Theorem 4: Algorithm 3 is $1/2$-competitive against $\mathrm{OPT}_{\text{offline-MP}}$, and no policy does better (corrected: atomless value laws with finite mean)
-- statement:
--   In two-stage stochastic joint matching and pricing, with market efficiency $\mathbb E[\mathrm{OBJ}_{D_1\cup D_2}+\mathrm{OBJ}_S]$ (Definition 3):
--
--   1. On every instance whose second-stage value laws $F_i$ (on $[0,\infty)$) are atomless with finite mean, every run of Algorithm 3 (Ex Ante Pricing with Simulation & Discarding) satisfies
--   $$\mathbb E\big[\mathrm{OBJ}_{D_1\cup D_2}+\mathrm{OBJ}_S\big]\ \ge\ \frac12\,\mathrm{OPT}_{\text{offline-MP}},$$
--   so $\Gamma_{\text{matching-pricing}}(\text{Algorithm 3},\mathrm{OPT}_{\text{offline-MP}})\ge1/2$.
--   2. For every $\delta>0$ there is such an instance with $\mathrm{OPT}_{\text{offline-MP}}>0$ on which every matching/pricing policy, deterministic or randomized, has market efficiency at most $(1/2+\delta)\,\mathrm{OPT}_{\text{offline-MP}}$. Hence no policy obtains a competitive ratio better than $1/2$.
--
--   The pair shows that pricing the second-stage demands from the ex ante relaxation and resolving first-stage conflicts by discarding is optimal against the offline benchmark.
--
--   Differences from the source:
--   - correction: Lemma 4, Theorem 4 and Theorem EC.4 are stated for arbitrary value laws F_i, with T_i(q) ≜ argmax{t : 1 − F_i(t) ≥ q} and the claim that i accepts the price T_i(y_i) with probability y_i (p.27) → every second-stage law F_i is atomless with finite mean (MPInstance.Regular); reason: for a law with an atom the argmax does not exist and no price is accepted with probability y_i: for a point mass at 1 and any q ∈ (0,1), {t : 1 − F(t) ≥ q} = (−∞, 1) has no maximum and every price is accepted with probability 0 or 1; a finite mean is needed for w_i(p) = E[v | v ≥ p] to be a real number. Excluded: laws with atoms and laws with infinite mean
--   - reading: values v_i ∼ F_i of demands for the service (p.8), never given a sign → each F_i is carried by [0, ∞); reason: a value for the service is a non-negative willingness to pay; the paper's welfare objective, its examples (uniform values, the two-point law on {0, 1/ε}) and its formula w_i(T_i(y))y = ∫_0^y T_i(q)dq all use non-negative values
--   - encoding: first-stage demands carry a law F_i and an accepted price p_i, contributing w_i(p_i) → each first-stage demand carries ŵ_i = w_i(p_i) ≥ 0 directly; reason: only w_i(p_i) enters the problem, and every ŵ_i ≥ 0 is w_i(p_i) for some law and price (a point mass at ŵ_i), so the instances are the same
--   - generalization: price p_i = T_i(y_i) also at y_i = 0, where argmax{t : 1 − F_i(t) ≥ 0} does not exist → the price of a demand with y_i = 0 is arbitrary; reason: the paper's algorithm is undefined there; the Lean statement holds for every choice, so it covers any convention
--   - encoding: Γ_matching-pricing(Algorithm 3, OPT_offline-MP) ≥ 1/2 → efficiency ≥ OPT_offline-MP/2 on every instance, for every run; reason: the minimum of the ratio over instances with OPT > 0 is at least 1/2 iff every such instance satisfies the inequality; it is trivial when OPT = 0
--   - generalization: no other matching/pricing policy obtains a better competitive ratio (for every policy, some instances have ratio near 1/2; the paper's instance has an atomic two-point law) → for every δ > 0 one instance, with atomless finite-mean laws, on which every policy has efficiency ≤ (1/2 + δ)·OPT; reason: one instance defeating all policies at once implies that every policy has ratio at most 1/2, and it lies in the class of clause (a)
--   - encoding: randomized policies → a probability space (Ω, μ) with a deterministic policy for each outcome, independent of the values; efficiency ∫ (π ω).efficiency dμ; reason: a policy's randomness is independent of the values and its expected efficiency is the average over its deterministic realizations
--   - reading: sample a supply vertex j† from {x_ij}_{j ∈ S} → j is sampled with probability x_ij and no supply with probability 1 − y_i; reason: Σ_j x_ij = y_i ≤ 1, so {x_ij} is a sub-probability vector; the recommendation probabilities x_ij used in the proof (p.27) are those
-- source:
--   Feng, Niazadeh & Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1, Theorem 4, p.26; Algorithm 3, p.27; proof pp.26–27

import Mathlib
import Definitions.Def_TwoStageMatch_Supplement_Algorithm3

open MeasureTheory

universe u

namespace TwoStageMatch.Supplement

/-- **Theorem 4** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, p.26; proof pp.26–27).
`Γ_matching-pricing(Algorithm 3, OPT_offline-MP) ≥ 1/2`, and no other matching/pricing policy can
obtain a better competitive ratio against `OPT_offline-MP`.

* (a) On every joint matching/pricing instance whose second-stage value laws are atomless with
  finite mean, every run of Algorithm 3 has expected market efficiency at least
  `(1/2) · OPT_offline-MP`.
* (b) For every `δ > 0` there is such an instance with `OPT_offline-MP > 0` on which every
  matching/pricing policy, deterministic or randomized, has expected market efficiency at most
  `(1/2 + δ) · OPT_offline-MP`.

**Formalization Note.** `Γ ≥ 1/2` is stated per instance (`ALG ≥ OPT/2` on every instance), which
is the minimum of Definition 3 over the instances with `OPT > 0`. Clause (b) gives one instance
that defeats every policy at once, which implies that every policy has ratio at most `1/2`. A
randomized policy is a probability space `(Ω, μ)` and a deterministic policy `π ω` for each
outcome, independent of the values; its efficiency is `∫ (π ω).efficiency dμ`. -/
theorem theorem_4 :
    (∀ {D₁ D₂ S : Type u} [Fintype D₁] [Fintype D₂] [Fintype S]
      [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S] (I : MPInstance D₁ D₂ S),
        I.Regular → ∀ r : Run3 I, (1 / 2 : ℝ) * optOfflineMP I ≤ r.efficiency) ∧
    (∀ δ : ℝ, 0 < δ → ∃ (n₁ n₂ m : ℕ) (I : MPInstance (Fin n₁) (Fin n₂) (Fin m)),
      I.Regular ∧ 0 < optOfflineMP I ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (π : Ω → DetPolicy I),
        ∫ ω, (π ω).efficiency ∂μ ≤ (1 / 2 + δ) * optOfflineMP I) := by sorry

end TwoStageMatch.Supplement
