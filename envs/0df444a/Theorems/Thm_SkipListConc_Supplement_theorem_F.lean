-- Prove2me | Theorems.Thm_SkipListConc_Supplement_theorem_F
-- name    : SkipListConc.Supplement.theorem_F
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:04:08.738727+00:00
-- url     : https://prove2.me/theorems/330185f5-a4d5-427c-8c47-e04f001d5bf6
-- title:
--   Theorem F — dynamic optimality for stationary and piecewise-stationary sources against $\mathrm{OPT}_{WB}$
-- statement:
--   Throughout, $0<p<1$, $b=1/p$, and heights follow Definition 1.1 (part (a)) or Definition 1.1 with epochal reseeding (Definition 1.6, part (b)). There is a constant $C_0=C_0(p)>0$ such that for every integer $K\ge1$ and every integer $B\ge2$ there is a constant $C=C(p,K,B)>0$ with the following property. Let the structure hold a fixed set of $n\ge2$ items, inserted (in any order) before the accesses, and serve $m$ accesses $X=(X_1,\dots,X_m)$, independent of the heights, so $F=n+m$; probabilities and expectations are over the accesses and the heights together. Let $\mathrm{cost}(X)$ be the structure's cost in the model of [BDL08] (finger moves plus height changes, plus rebuilds under reseeding) and $\mathrm{OPT}_{WB}(X)$ the weakly $B$-bounded offline optimum. The high-probability statements assume $0<\delta<1$ and $m\ge C_0\log_2^2(n+m)\log(1/\delta)$.
--
--   **(a)** For a stationary source,
--   $$
--   \mathbb E[\mathrm{cost}(X)]\le C\bigl(\mathbb E[\mathrm{OPT}_{WB}(X)]+n\log_2(n+m)\bigr),
--   $$
--   and with probability at least $1-4\delta$,
--   $$
--   \mathrm{cost}(X)\le C\Bigl(1+\log\frac1\delta\Bigr)\bigl(\mathrm{OPT}_{WB}(X)+n\log_2(n+m)\bigr).
--   $$
--
--   **(b)** For a piecewise-stationary source with $P$ phases, under Definition 1.6,
--   $$
--   \mathbb E[\mathrm{cost}(X)]\le C\Bigl(\mathbb E[\mathrm{OPT}_{WB}(X)]+n\log_2(n+m)+m\log_2\Bigl(1+\frac{nP}{m}\Bigr)\Bigr),
--   $$
--   and with probability at least $1-3\delta$,
--   $$
--   \mathrm{cost}(X)\le C\Bigl(\mathrm{OPT}_{WB}(X)+n\log_2(n+m)+m\log_2\Bigl(1+\frac{nP}{m}\Bigr)+n\log\frac1\delta\Bigr).
--   $$
--
--   This is dynamic optimality in the weakly bounded class of [BDL08] for stationary sources, in expectation, and under reseeding with high probability.
--
--   Differences from the source:
--   - encoding: n items inserted before the accesses; accesses X_i to the items → insertion list ins (Nodup, any order, length n ≥ 2); accesses X i : Ω → Fin n indexing ins; σ_X = ins ++ accessList ins X; reason: the items and their insertion order are arbitrary
--   - encoding: the source is independent of the structure's random choices; probabilities over accesses and heights together → one probability space carrying X and the height noise, with IndepFun between the access vector and the noise; reason: the source's model (p.11)
--   - encoding: every key set, probability space → key type α : Type and sample space Ω : Type; reason: the constants are chosen before these types, which fixes their universe; every concrete instance lives there
--   - encoding: constants C₀ = C₀(p) and O_{p,K,B}(·) → ∃ C₀ > 0 after p only; ∃ C > 0 after p, K, B, one C for the expectation and the high-probability statement of each part; reason: taking the larger constant is equivalent
--   - reading: B ≥ 2 a constant → B a natural number ≥ 2; reason: [BDL08]'s B counts items per level
--   - reading: cost(X), the cost of our structure in the [BDL08] model → finger moves cost_t − 1 of every operation of σ_X, insertions included, plus height changes (∑_x H_x(f_x) without reseeding; |new − old| at redraws, insertion draws at full height, plus rebuild costs under reseeding); reason: the cost model of p.35; counting the insertions' searches is what p.35 says ('part of the additive term')
--   - reading: OPT_WB(X): least cost of a weakly B-bounded skip list that knows X and may raise or lower, at unit cost per level, the height of any item its search touches → OPTWB: infimum over sequences of weakly B-bounded configurations, free initial configuration, search paying searchCost − 1, changes only at items the search stepped onto, |change| per level; insertions not paid; reason: the definition of pp.11, 35
--   - encoding: E[·] → lower Lebesgue integral ∫⁻ of the ℕ-valued cost and optimum; reason: no integrability assumption can make the bound vacuous
--   - encoding: piecewise stationary with P phases → IsPiecewiseStationarySource: independent accesses, a monotone phase map Fin m → Fin P and one law per phase; reason: consecutive blocks; an empty phase only overcounts P, and the bound is increasing in P
--   - encoding: log₂, log₂²(n+m), log(1/δ) → Real.logb 2, (Real.logb 2 (n+m))², natural logarithm; reason: notation
--   - encoding: nP/m with m ≥ 1 implicit → real division, at m = 0 the term m·log₂(1 + nP/m) is 0; reason: the term is multiplied by m
--   - encoding: "with probability at least 1 − 4δ (3δ)" → P{cost(X) > bound} ≤ 4δ (3δ); reason: complement
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Theorem F, p.11; model §5.3, pp.34–35

import Mathlib
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_Supplement_costXa
import Definitions.Def_SkipListConc_Supplement_costXb
import Definitions.Def_SkipListConc_Supplement_OPTWB
import Definitions.Def_SkipListConc_Supplement_accessList
import Definitions.Def_SkipListConc_Supplement_IsStationarySource
import Definitions.Def_SkipListConc_Supplement_IsPiecewiseStationarySource

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SkipListConc.Supplement

/-- Theorem F (dynamic optimality for stationary sources) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Theorem F, p.11). Let the
data structure hold a fixed set of `n ≥ 2` items, inserted before the accesses, and serve `m`
accesses, so that `F = n + m`, and let `B ≥ 2` be a constant. The probabilities are over the
random accesses and the random heights together, and the high-probability statements assume
`m ≥ C₀ log₂²(n + m) log(1/δ)` for a constant `C₀ = C₀(p)`.
(a) For a stationary source, `E[cost(X)] = O_{p,K,B}(E[OPT_WB(X)] + n log₂(n + m))`, and with
probability at least `1 − 4δ`, `cost(X) = O_{p,K,B}((1 + log(1/δ))(OPT_WB(X) + n log₂(n + m)))`.
(b) For a piecewise-stationary source with `P` phases, under Definition 1.6,
`E[cost(X)] = O_{p,K,B}(E[OPT_WB(X)] + n log₂(n + m) + m log₂(1 + nP/m))`, and with probability
at least `1 − 3δ`, `cost(X) = O_{p,K,B}(OPT_WB(X) + n log₂(n + m) + m log₂(1 + nP/m) + n log(1/δ))`.

**Formalization Note** `C₀` is chosen after `p` only; the constant `C` after `p, K, B` (one
for the expectation and the high-probability statement of each part, which is equivalent to two).
The items are the entries of the insertion list `ins` (any order), the accesses are indices
`X i` into it, `σ_X = ins ++ accessList ins X`, and `X` is independent of the height noise
(`IndepFun`). Expectations are lower Lebesgue integrals of `ℕ`-valued costs. `cost(X)` is
`costXa` (no reseeding) or `costXb` (reseeded, noise indexed by `((item, epoch), draw)`);
`OPT_WB` is `OPTWB`. `log₂` is `Real.logb 2`, `log` the natural logarithm. -/
theorem theorem_F (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ K : ℕ, 1 ≤ K → ∀ B : ℕ, 2 ≤ B → ∃ C : ℝ, 0 < C ∧
      (∀ {α : Type} [LinearOrder α] (ins : List α), ins.Nodup → 2 ≤ ins.length →
        ∀ (m : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μJ : Measure (ℕ → Fin K))
        (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (X : Fin m → Ω → Fin ins.length),
        IsPromotionNoise p K μJ P ξ → IsStationarySource P X →
        IndepFun (fun ω i => X i ω) (fun ω k => ξ k ω) P →
          ∫⁻ ω, (costXa p ξ (ins ++ accessList ins (fun i => X i ω)) ω : ℝ≥0∞) ∂P ≤
              ENNReal.ofReal C * (∫⁻ ω, ((OPTWB B ins.toFinset (accessList ins (fun i => X i ω))) : ℝ≥0∞) ∂P +
                ENNReal.ofReal ((ins.length : ℝ) * Real.logb 2 ((ins.length : ℝ) + m))) ∧
          ∀ δ : ℝ, 0 < δ → δ < 1 → C0 * Real.logb 2 ((ins.length : ℝ) + m) ^ 2 * Real.log (1 / δ) ≤ m →
            P {ω | C * (1 + Real.log (1 / δ)) * (((OPTWB B ins.toFinset (accessList ins (fun i => X i ω))) : ℝ) + (ins.length : ℝ) * Real.logb 2 ((ins.length : ℝ) + m)) <
                (costXa p ξ (ins ++ accessList ins (fun i => X i ω)) ω : ℝ)} ≤ ENNReal.ofReal (4 * δ)) ∧
      (∀ {α : Type} [LinearOrder α] (ins : List α), ins.Nodup → 2 ≤ ins.length →
        ∀ (m : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μJ : Measure (ℕ → Fin K))
        (ξ : (α × ℕ) × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (Ph : ℕ) (X : Fin m → Ω → Fin ins.length),
        IsPromotionNoise p K μJ P ξ → IsPiecewiseStationarySource P X Ph →
        IndepFun (fun ω i => X i ω) (fun ω k => ξ k ω) P →
          ∫⁻ ω, (costXb p ξ (ins ++ accessList ins (fun i => X i ω)) ω : ℝ≥0∞) ∂P ≤
              ENNReal.ofReal C * (∫⁻ ω, ((OPTWB B ins.toFinset (accessList ins (fun i => X i ω))) : ℝ≥0∞) ∂P +
                ENNReal.ofReal ((ins.length : ℝ) * Real.logb 2 ((ins.length : ℝ) + m) +
                  m * Real.logb 2 (1 + (ins.length : ℝ) * Ph / m))) ∧
          ∀ δ : ℝ, 0 < δ → δ < 1 → C0 * Real.logb 2 ((ins.length : ℝ) + m) ^ 2 * Real.log (1 / δ) ≤ m →
            P {ω | C * (((OPTWB B ins.toFinset (accessList ins (fun i => X i ω))) : ℝ) + (ins.length : ℝ) * Real.logb 2 ((ins.length : ℝ) + m) +
                    m * Real.logb 2 (1 + (ins.length : ℝ) * Ph / m) + (ins.length : ℝ) * Real.log (1 / δ)) <
                (costXb p ξ (ins ++ accessList ins (fun i => X i ω)) ω : ℝ)} ≤ ENNReal.ofReal (3 * δ)) := by sorry

end SkipListConc.Supplement
