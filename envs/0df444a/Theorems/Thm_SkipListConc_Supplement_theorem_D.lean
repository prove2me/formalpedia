-- Prove2me | Theorems.Thm_SkipListConc_Supplement_theorem_D
-- name    : SkipListConc.Supplement.theorem_D
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:02:44.088506+00:00
-- url     : https://prove2.me/theorems/07b74297-f6b7-42ac-bbc3-d7a6ec0c86e1
-- title:
--   Theorem D — lower bound $\Pr[\sum_t\mathrm{cost}_t\ge cFu]\ge c\,p^u$ for every rule with (T1)–(T4)
-- statement:
--   Fix $0<p<1$ and an integer $K\ge1$. Consider any promotion rule with properties (T1)–(T4) whose heights never decrease, on a linearly ordered key set with infinitely many keys. There are constants $c,C>0$ (depending on the rule) such that for every $n\ge2$ and $m\ge n^2$ there is an operation sequence $\sigma_{n,m}$ on $n$ items, of length $F=2m+2n$, with $\mathrm{Ent}(\sigma_{n,m})\le C\,F$ and, for every integer $u\ge1$,
--   $$
--   \Pr\Bigl[\sum_t\mathrm{cost}_t(x_t)\ge c\,F\,u\Bigr]\ \ge\ c\,p^{u}.
--   $$
--   Here $\mathrm{cost}_t(x_t)$ is the skip-list search cost with the heights of the rule (an item never operated on before at height $1$).
--
--   This shows that the confidence term $F\log(1/\delta)$ of Theorem C cannot be reduced in order: there are sequences with benchmark $O(F)$ on which the cost is at least a constant times $Fu$ with probability at least a constant times $p^u$.
--
--   Differences from the source:
--   - encoding: every promotion rule with properties (T1) to (T4) whose heights never decrease → a height process H : α → ℕ → Ω → ℕ with IsTRule (measurable integer heights ≥ 1, (T1)–(T4) in the forms of Lemmas 2.2, 2.5, 3.6(iii), non-decreasing); reason: the rule enters the theorem only through its heights and these properties
--   - encoding: sequences on n items for every n → linearly ordered key type with Infinite α; reason: a finite key set has no sequence on n items for large n
--   - encoding: constants c_{p,K}, C_{p,K} > 0 "for every promotion rule … there are constants" → ∃ c C > 0 after the rule; reason: the source's quantifier order
--   - reading: for every n ≥ 2, m ≥ n² and integer u ≥ 1 there is a sequence σ_{n,m} → ∃ σ for each n, m, chosen before ∀ u; reason: the name σ_{n,m} carries no u and the proof's sequence (p.31) does not depend on u; this reading implies the other
--   - encoding: cost_t(x_t) → searchCost with the rule's heights, height 1 before an item's first operation; reason: the source's cost (pp.4–5) and the convention H_x(0) = 1 (p.5)
--   - encoding: (T2) "a Morris counter coupled to the process" → a Morris chain M_y on the same probability space with M_y(j) ≤ H_y(j) surely; reason: a coupling on an extension space is turned into this by running the theorem on the extension, where the heights and the cost event keep their laws
--   - encoding: (T3) "given the item's own trajectory cut off at ℓ" → multiplied-form bound for every horizon N ≥ j and every value τ of (min(H_y(i), ℓ))_{1≤i≤N} with τ_j = ℓ; reason: heights never decrease, so the cut-off values after j carry no information, and the conditional bound on values of positive probability is the multiplied form
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Theorem D, p.9 (σ_{n,m} on p.31)

import Mathlib
import Definitions.Def_SkipListConc_entropy
import Definitions.Def_SkipListConc_Supplement_IsTRule
import Definitions.Def_SkipListConc_Supplement_ruleTotalCost

open MeasureTheory ProbabilityTheory

namespace SkipListConc.Supplement

/-- Theorem D (lower bound for the confidence term) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Theorem D, p.9). For every promotion
rule with properties (T1) to (T4) whose heights never decrease, there are constants
`c_{p,K}, C_{p,K} > 0` such that for every `n ≥ 2`, `m ≥ n²` and integer `u ≥ 1` there is a
sequence `σ_{n,m}` on `n` items with `F = 2m + 2n`, `Ent(σ_{n,m}) ≤ C_{p,K} F` and
`Pr[∑_t cost_t(x_t) ≥ c_{p,K} F u] ≥ c_{p,K} p^u`.

**Formalization Note** The rule is a height process `H` satisfying `IsTRule` on a linearly
ordered key type with infinitely many keys (so that sequences on `n` items exist for every `n`);
the constants are chosen after the rule, and `σ_{n,m}` before `u` (its name carries no `u`).
The cost of a search is the published `searchCost` with the heights of the rule
(`ruleTotalCost`). -/
theorem theorem_D (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (K : ℕ) (hK : 1 ≤ K)
    {α : Type} [LinearOrder α] [Infinite α] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (H : α → ℕ → Ω → ℕ) (hH : IsTRule p K P H) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ n m : ℕ, 2 ≤ n → n ^ 2 ≤ m →
        ∃ σ : List α, σ.toFinset.card = n ∧ σ.length = 2 * m + 2 * n ∧
          entropy p σ ≤ C * σ.length ∧
          ∀ u : ℕ, 1 ≤ u →
            ENNReal.ofReal (c * p ^ u) ≤
              P {ω | c * σ.length * u ≤ (ruleTotalCost H σ ω : ℝ)} := by sorry

end SkipListConc.Supplement
