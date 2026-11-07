-- Prove2me | Theorems.Thm_ReplicableDecisions_theorem_3_1
-- name    : ReplicableDecisions.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:08:53.475782+00:00
-- url     : https://prove2.me/theorems/46f2dd37-77f8-4e2a-a0c9-9f7cd6205173
-- title:
--   Theorem 3.1 — binary sample complexity: $\frac1{4608s_\rho^2}<n^\star(\beta,\rho)\le\lceil\log(M/\delta)/s_\rho^2\rceil$
-- statement:
--   Let $\mathcal P$ be a known finite experiment with $M$ models and outputs $\mathcal Y=\{0,1\}$, with acceptable sets $\emptyset\ne\Gamma(P)\subseteq\mathcal Y$ and both forced classes $A_0,A_1$ nonempty. Let $0<\beta\le1/8$, $0<\rho\le1/16$ and $\delta=\min\{\beta,\rho/4\}$. Then $n^\star(\beta,\rho)$ is finite and
--
--   $$
--   \frac1{4608\,s_\rho^2}<n^\star(\beta,\rho)\le\left\lceil\frac{\log(M/\delta)}{s_\rho^2}\right\rceil .
--   $$
--
--   Moreover:
--
--   1. $n^\star(\beta,\rho)\ge\log(1/(4\beta))/(-2\log(1-s_1^2))$, read as zero if $s_1=1$.
--   2. The upper bound is attained by maximum likelihood followed by a shared random breadth-first threshold on $G_{<s_\rho}$: with $n_0=\lceil\log(M/\delta)/s_\rho^2\rceil$, this rule is a $(\beta,\rho)$-valid $n_0$-sample algorithm.
--   3. It uses at most $\lceil4608\,n^\star(\beta,\rho)\log(M/\delta)\rceil$ samples, that is, $n_0$ is at most this number.
--
--   The theorem determines, up to a factor $\log(M/\delta)$, the sample size of replicable binary decisions in every finite experiment by the one scale $s_\rho$, and it attains the bound with one explicit rule that depends only on the probability tables and the acceptable sets.
--
--   **Formalization Note** $n^\star$ is a natural number $N$ asserted to be the least element of the set of feasible sample sizes, so its finiteness is a conclusion.
--
--   Differences from the source:
--   - encoding: a known family P = {P1, …, PM} of distinct distributions on a finite set Z → an `Experiment ι Z`: an injective table of probability vectors over a finite index type, with Z in `Type` and M = `Fintype.card ι`; reason: models are named by index; the reused Bhattacharyya coefficient takes a type in `Type`, which loses no finite Z
--   - encoding: probabilities over S, S′ ∼ Pⁿ and the seed R → finite sums over samples `Fin n → Z` of products of table entries times seed-measure terms `μ.real`; reason: the data side is finite; the same numbers
--   - encoding: Y = {0, 1} → `Bool`, with 0 = `false` and 1 = `true`; reason: same two outputs
--   - encoding: s_L as a minimum over chains Q0, …, Qℓ → `sInf` of the finite nonempty value set, chains as `Fin (ℓ + 1) → ι`; reason: under A0, A1 ≠ ∅ and L ≥ 1 the set is finite and nonempty, and a proved sanity check shows that the infimum is attained
--   - generalization: a maximum-likelihood model with fixed tie-breaking → any function `mle` of the sample selecting a likelihood maximizer; reason: the proof bounds the event pointwise in the sample and never uses how ties are broken; every fixed tie-breaking is such a function
--   - reading: "shared random breadth-first threshold" when D = ∞, where the proof uses a neighborhood-correct component labeling (p.12) → the selector 1{d(P) = ∞} with a trivial seed; reason: it is a breadth-first threshold, as the sentence says, neighborhood correct with empty boundary, and differs from the printed labeling only on components meeting neither class, where the label is an arbitrary choice
--   - encoding: seed spaces of an algorithm in n⋆; the rule's seed → `Ω : Type` in `validSampleSizes`; the rule's seed on `ℕ` with the uniform law on the odd thresholds; reason: the page notes that arbitrary seed spaces offer no additional power
--   - encoding: n⋆(β, ρ) = min{…} → `∃ N : ℕ, IsLeast (validSampleSizes E Γ β ρ) N`; reason: a genuine finite minimum; finiteness is implied by the printed upper bound
--   - encoding: A : Zⁿ × R → Y measurable in its seed, seed law a probability → `IsValid` bundles `IsProbabilityMeasure μ` and every `{ω | A x ω = y}` measurable; reason: on the finite Y this is measurability in the seed; part of the page's definition of an algorithm
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), Theorem 3.1, (3.1), p.10 (PDF p.12)

import Mathlib
import Definitions.Def_ReplicableDecisions_IsValid
import Definitions.Def_ReplicableDecisions_hopSeparation
import Definitions.Def_ReplicableDecisions_weakGraph
import Definitions.Def_ReplicableDecisions_IsMaxLikelihood
import Definitions.Def_ReplicableDecisions_thresholdRule
import Definitions.Def_ReplicableDecisions_confidenceBound

namespace ReplicableDecisions

/-- **Theorem 3.1 (Binary sample complexity).** Chen, *Replicable Decisions in Finite Experiments*, STOC
2027 submission (sha256 52d181db…), Theorem 3.1, (3.1), p.10 (PDF p.12). For a known finite experiment
with `Y = {0, 1}`, `A₀, A₁ ≠ ∅`, `0 < β ≤ 1/8`, `0 < ρ ≤ 1/16`, `δ = min{β, ρ/4}`:
`1/(4608 s_ρ²) < n⋆(β, ρ) ≤ ⌈log(M/δ)/s_ρ²⌉`. Moreover `n⋆(β, ρ) ≥ log(1/(4β))/(−2 log(1 − s₁²))`, read as
zero if `s₁ = 1`. The upper bound is attained by maximum likelihood followed by a shared random
breadth-first threshold on `G_{<s_ρ}`, and it uses at most `⌈4608 n⋆(β, ρ) log(M/δ)⌉` samples.

**Formalization Note.** `N` is `n⋆`: `IsLeast` makes it a genuine finite minimum. `Y = {0, 1}` is `Bool`,
with `0 = false` and `1 = true`. The upper-bound clause is about the concrete rule `thresholdRule`, for
every selection `mle` of a likelihood maximizer. When `D = ∞` the rule's selector is `1{d = ∞}`. -/
theorem theorem_3_1 {ι : Type*} {Z : Type} [Fintype ι] [Fintype Z] (E : Experiment ι Z)
    (Γ : ι → Set Bool) (hΓ : ∀ i, (Γ i).Nonempty) (hA₀ : (forcedClass Γ false).Nonempty)
    (hA₁ : (forcedClass Γ true).Nonempty) {β ρ : ℝ} (hβ₀ : 0 < β) (hβ : β ≤ 1 / 8) (hρ₀ : 0 < ρ)
    (hρ : ρ ≤ 1 / 16) :
    let δ : ℝ := min β (ρ / 4)
    let M : ℝ := Fintype.card ι
    let s₁ : ℝ := hopSeparation E Γ 1
    let sρ : ℝ := hopSeparation E Γ (hopBudget ρ)
    let n₀ : ℕ := ⌈Real.log (M / δ) / sρ ^ 2⌉₊
    ∃ N : ℕ, IsLeast (validSampleSizes E Γ β ρ) N ∧
      1 / (4608 * sρ ^ 2) < (N : ℝ) ∧
      N ≤ n₀ ∧
      confidenceBound β s₁ ≤ (N : ℝ) ∧
      (∀ mle : (Fin n₀ → Z) → ι, IsMaxLikelihood E mle →
        IsValid E Γ β ρ (thresholdSeedLaw (strictGraph E sρ) Γ)
          (thresholdRule (strictGraph E sρ) Γ mle)) ∧
      n₀ ≤ ⌈4608 * (N : ℝ) * Real.log (M / δ)⌉₊ := by sorry

end ReplicableDecisions
