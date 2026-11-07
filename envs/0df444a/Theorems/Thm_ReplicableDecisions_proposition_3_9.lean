-- Prove2me | Theorems.Thm_ReplicableDecisions_proposition_3_9
-- name    : ReplicableDecisions.proposition_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:08:48.23572+00:00
-- url     : https://prove2.me/theorems/80da8187-4a47-4306-b5c6-e5e29b953f23
-- title:
--   Proposition 3.9 — confidence lower bound: $(1-s_1^2)^{2n}\le4\beta$
-- statement:
--   Let $A_0,A_1\ne\emptyset$ and $0<\beta<1/4$. Any algorithm accurate with error at most $\beta$ on $A_0\cup A_1$ satisfies
--
--   $$
--   (1-s_1^2)^{2n}\le4\beta .
--   $$
--
--   Consequently, for every $\rho$,
--
--   $$
--   n^\star(\beta,\rho)\ge\frac{\log(1/(4\beta))}{2\log(1/(1-s_1^2))},
--   $$
--
--   where the right side is interpreted as zero if $s_1=1$. If $s_1^2\le1/2$, this right side is at least $\log(1/(4\beta))/(4s_1^2)$.
--
--   The first assertion needs no replication hypothesis. Together, the three supply the dependence on $\beta$ that the chain bound does not see.
--
--   Differences from the source:
--   - encoding: a known family P = {P1, …, PM} of distinct distributions on a finite set Z → an `Experiment ι Z`: an injective table of probability vectors over a finite index type, with Z in `Type` and M = `Fintype.card ι`; reason: models are named by index; the reused Bhattacharyya coefficient takes a type in `Type`, which loses no finite Z
--   - encoding: probabilities over S, S′ ∼ Pⁿ and the seed R → finite sums over samples `Fin n → Z` of products of table entries times seed-measure terms `μ.real`; reason: the data side is finite; the same numbers
--   - encoding: A : Zⁿ × R → Y measurable in its seed → `A : (Fin n → Z) → Ω → Y` with every `{ω | A x ω = y}` measurable, on an arbitrary probability space; reason: on a finite Y this is measurability in the seed
--   - encoding: Y = {0, 1} → `Bool`, with 0 = `false` and 1 = `true`; reason: same two outputs
--   - encoding: s_L as a minimum over chains Q0, …, Qℓ → `sInf` of the finite nonempty value set, chains as `Fin (ℓ + 1) → ι`; reason: under A0, A1 ≠ ∅ and L ≥ 1 the set is finite and nonempty, and a proved sanity check shows that the infimum is attained
--   - encoding: n⋆(β, ρ) ≥ the bound, with min ∅ = +∞ → the bound holds for every member of `validSampleSizes E Γ β ρ`; reason: this is the bound on the minimum, and free when the set is empty
--   - encoding: denominator 2 log(1/(1 − s₁²)) → `-2 * Real.log (1 - s ^ 2)` inside `confidenceBound`; reason: the same number
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), Proposition 3.9, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_ReplicableDecisions_IsValid
import Definitions.Def_ReplicableDecisions_hopSeparation
import Definitions.Def_ReplicableDecisions_confidenceBound

open MeasureTheory

namespace ReplicableDecisions

/-- **Proposition 3.9 (Confidence lower bound).** Chen, *Replicable Decisions in Finite Experiments*,
STOC 2027 submission (sha256 52d181db…), Proposition 3.9, p.14 (PDF p.16). Let `A₀, A₁ ≠ ∅` and
`0 < β < 1/4`. Any algorithm accurate with error at most `β` on `A₀ ∪ A₁` has `(1 − s₁²)^{2n} ≤ 4β`.
Consequently, for every `ρ`, `n⋆(β, ρ) ≥ log(1/(4β)) / (2 log(1/(1 − s₁²)))`, read as zero if `s₁ = 1`.
If `s₁² ≤ 1/2`, this is at least `log(1/(4β))/(4s₁²)`.

**Formalization Note.** The first assertion has no replication hypothesis and covers every `n`, including
`n = 0`, and every seed space. The second holds for every member of `validSampleSizes`, which gives the
bound on the minimum whenever it exists; when the set is empty, `n⋆ = +∞` and the bound is free. -/
theorem proposition_3_9 {ι : Type*} {Z : Type} [Fintype ι] [Fintype Z] (E : Experiment ι Z)
    (Γ : ι → Set Bool) (hΓ : ∀ i, (Γ i).Nonempty) (hA₀ : (forcedClass Γ false).Nonempty)
    (hA₁ : (forcedClass Γ true).Nonempty) {β : ℝ} (hβ₀ : 0 < β) (hβ : β < 1 / 4) :
    (∀ (n : ℕ) (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : (Fin n → Z) → Ω → Bool), IsSeedMeasurable A →
        (∀ i ∈ forcedClass Γ false ∪ forcedClass Γ true, err E Γ μ A i ≤ β) →
        (1 - hopSeparation E Γ 1 ^ 2) ^ (2 * n) ≤ 4 * β) ∧
      (∀ ρ : ℝ, ∀ n ∈ validSampleSizes E Γ β ρ, confidenceBound β (hopSeparation E Γ 1) ≤ n) ∧
      (hopSeparation E Γ 1 ^ 2 ≤ 1 / 2 →
        Real.log (1 / (4 * β)) / (4 * hopSeparation E Γ 1 ^ 2) ≤
          confidenceBound β (hopSeparation E Γ 1)) := by sorry

end ReplicableDecisions
