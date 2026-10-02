-- Prove2me | Theorems.Thm_ServiceParts_Shortfall_shortfall_exponential_tail
-- name    : ServiceParts.Shortfall.shortfall_exponential_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T23:32:03.925039+00:00
-- url     : https://prove2.me/theorems/c5496e78-e245-4961-9274-5a223d242e9b
-- title:
--   Theorem 11 (Glasserman), corrected — P{V > v} ~ β e^{−αv}, α the positive root of E[e^{−α(c−D)}] = 1
-- statement:
--   Consider the capacity-limited system of Section 8.1: nonnegative i.i.d. demands $D_1, D_2, \dots$ with generic demand $D$, capacity $c$ and $E[D] < c$, and the stationary shortfall
--   $$V = \sup_{n \ge 0} \sum_{k=1}^{n} (D_k - c).$$
--   Assume
--
--   1. there is $\delta > 0$ with $E[e^{\alpha D}] < \infty$ for all $\alpha < \delta$;
--   2. $P[D > c] > 0$;
--   3. (correction) the law of $D$ is non-lattice;
--   4. (correction) the equation $E[e^{-\alpha(c - D)}] = 1$ has a solution $\alpha \in (0, \delta)$.
--
--   Then there exist constants $\beta > 0$ and $\alpha > 0$ such that
--   $$\frac{P\{V > v\}}{\beta e^{-\alpha v}} \longrightarrow 1 \qquad (v \to \infty),$$
--   and $\alpha$ is the unique strictly positive solution of $E[e^{-\alpha(c - D)}] = 1$.
--
--   The theorem says that the stationary shortfall of a capacity-limited system has an exactly exponential tail, with decay rate determined by the demand distribution and the capacity alone. This is the justification the book gives for approximating the shortfall by a mass-exponential law, from which target stock levels are set.
--
--   **Formalization Note** The printed statement is false without hypotheses 3 and 4. For integer-valued demand, $P\{V > v\}$ is a step function of $v$ and cannot be asymptotic to $\beta e^{-\alpha v}$ (a lattice law gives a different constant along each residue class). If $E[e^{\alpha D}]$ is finite only for $\alpha < \delta$, the equation $E[e^{-\alpha(c-D)}] = 1$ may have no root in $(0, \delta)$, and then no exponential rate exists. Both hypotheses are added and labelled. Section 8.1.3's demand (an atom at $0$ plus a density) is non-lattice. $\beta$ and $\alpha$ are fixed before $v$ and $\beta > 0$ is asserted, so the ratio is never a division by zero. $V$ is the maximum of the random walk, identified with the stationary shortfall by the milestone of Section 8.1.1. The approximation $\beta \approx e^{-2(.583)(c - E(D))/\sigma}$ for normal demand is not part of the statement.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 191, Theorem 11 (after Glasserman [95]); standing assumptions pp. 184-185, Section 8.1.1

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_ShortfallModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ServiceParts.Shortfall

/-- Theorem 11 (Glasserman), Muckstadt (2005), p. 191, with the two hypotheses the printed
statement omits (marked "correction"). Let `E[D] < c` (standing assumption), `E[e^{αD}] < ∞` for
all `α < δ` with `δ > 0`, and `P[D > c] > 0`; assume further (correction i) that the law of `D`
is non-lattice and (correction ii) that `E[e^{−α(c−D)}] = 1` has a root in `(0, δ)`. Then there
exist `β > 0` and `α > 0`, not depending on `v`, with `P{V > v} / (β e^{−αv}) → 1` as `v → ∞`,
where `V` is the stationary shortfall; and `α` is the unique strictly positive solution of
`E[e^{−α(c−D)}] = 1`. -/
theorem shortfall_exponential_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ShortfallModel Ω P) (δ : ℝ) (hδ : 0 < δ)
    (hmgf : ∀ α : ℝ, α < δ → Integrable (fun ω => Real.exp (α * M.demand 1 ω)) P)
    (hexceed : 0 < P {ω | M.capacity < M.demand 1 ω})
    (hnonlattice : ¬ IsLattice (P.map (M.demand 1)))
    (hroot : ∃ α ∈ Set.Ioo 0 δ,
      ∫ ω, Real.exp (-α * (M.capacity - M.demand 1 ω)) ∂P = 1) :
    ∃ β α : ℝ, 0 < β ∧ 0 < α ∧
      Tendsto (fun v : ℝ =>
          (P {ω | v < M.stationaryShortfall ω}).toReal / (β * Real.exp (-α * v)))
        atTop (𝓝 1) ∧
      ∫ ω, Real.exp (-α * (M.capacity - M.demand 1 ω)) ∂P = 1 ∧
      ∀ α' : ℝ, 0 < α' →
        ∫ ω, Real.exp (-α' * (M.capacity - M.demand 1 ω)) ∂P = 1 → α' = α := by sorry

end ServiceParts.Shortfall
