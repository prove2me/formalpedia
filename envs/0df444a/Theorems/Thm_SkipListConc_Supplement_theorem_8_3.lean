-- Prove2me | Theorems.Thm_SkipListConc_Supplement_theorem_8_3
-- name    : SkipListConc.Supplement.theorem_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:05:01.205996+00:00
-- url     : https://prove2.me/theorems/b07a667d-4c72-41da-b921-3e9eb45e6c0a
-- title:
--   Theorem 8.3 — transfer of Theorems A–C, E, F to self-adjusting treaps and zip trees
-- statement:
--   Throughout, $0<p<1$, $b=1/p$, and the self-adjusting treap and the self-adjusting zip tree store with every item a priority that follows the height-based promotion rule (Definition 1.1) in place of the height; after each promotion the tree restores heap order (rotations, resp. one unzip), so at every time it is the equivalent tree of the skip list whose heights are the priorities. The **tree cost** of a charge is the number of nodes its tree search visits plus the number of ancestors the target moves past when its priority rises. Under reseeding (Definition 1.6) the tree redraws every priority at the start of each epoch and is rebuilt as a Cartesian tree, at one unit per item present.
--
--   Theorems A, B, C, E and F hold for both trees with the skip-list search cost, and in Theorem F the cost $\mathrm{cost}(X)$, replaced by the tree cost, with their own constants:
--
--   1. **(A)** for every $K\ge1$ there is $C=C(p,K)>0$ such that for every charge $t$, $\Pr[\mathrm{cost}^{\mathrm{tree}}_t(x_t)>C(a_t+u)]\le 3e^{-u}$ for all $u\ge0$, and $\mathrm{cost}^{\mathrm{tree}}_t(x_t)\le C(1+\log_b(t/f_t)+\log\frac1\delta)$ with probability at least $1-\delta$;
--   2. **(B)** for every $K\ge1$ there is $C>0$ with $\sum_t\mathrm{cost}^{\mathrm{tree}}_t\le C\,A(\sigma)(1+\log\frac1\delta)$ and $\le C\,\mathrm{Ent}(\sigma)(1+\log\frac1\delta)$, each with probability at least $1-\delta$;
--   3. **(C)** for every $K\ge1$ there is $C>0$ with
--   $$
--   \sum_t\mathrm{cost}^{\mathrm{tree}}_t(x_t)\le C\Bigl(\mathrm{Ent}(\sigma)+F\log\frac1\delta\Bigr)
--   $$
--   with probability at least $1-\delta$;
--   4. **(E)** under reseeding, for every $K\ge1$ there is $C>0$ with tree cost plus rebuilds at most $C(\mathrm{Ent}(\sigma)+n\log\frac1\delta)$ with probability at least $1-\delta$, and for every $\kappa>0$ a $C'$ with tree cost plus rebuilds at most $C'\,\mathrm{Ent}(\sigma)$ with probability at least $1-n^{-\kappa}$ when $n\ge2$ and every $f_x\ge2$;
--   5. **(F)** there is $C_0=C_0(p)$ such that for every $K\ge1$ and $B\ge2$ there is $C$ for which the four statements of Theorem F hold with $\mathrm{cost}(X)$ the tree cost of all operations of $\sigma_X$ (plus rebuilds under reseeding).
--
--   All quantifiers over key sets, sequences, probability spaces, jump laws, sources and $\delta$ are as in Theorems A, B, C, E and F.
--
--   This carries the concentration bounds of the paper from skip lists to binary search trees whose priorities adapt to the access frequencies.
--
--   Differences from the source:
--   - encoding: the self-adjusting treap and zip tree, priorities following Definition 1.1, search cost and restructuring (Lemma 8.2) → tree cost of a charge = nodes visited by the tree search in the equivalent tree + ancestors the target moves past (treeChargeCost); reason: both trees have the shape of the equivalent tree (p.41); the factor c_T between this count and rotations / pointer updates is absorbed by the constant
--   - encoding: constants larger by the factor c_T of Lemma 8.2 → existential constants chosen after the same parameters as in each transferred theorem (C after p, K; C' after p, K, κ; C₀ after p; C after p, K, B); reason: "larger by c_T" leaves every constant existential
--   - encoding: Theorems A to C, E and F hold for the two trees → one theorem, the conjunction of the five transferred statements; reason: each conjunct is the transferred theorem at full strength
--   - reading: under reseeding the tree is rebuilt from its keys in sorted order as a Cartesian tree in O(n) time → rebuild cost = number of items present at each epoch start (treeReseededCost); reason: the source's accounting (p.42)
--   - reading: Theorem F's cost(X) read as the tree cost including restructuring → treeTotalCost / treeReseededCost of all operations of σ_X, insertions included; reason: p.42; counting the insertions only enlarges the cost
--   - generalization: part E, first sentence: each item with f_x ≥ 2 → first sentence without f_x ≥ 2; reason: the skip-list bound does not use f_x ≥ 2 (p.34) and the transfer is per charge; specializes to the source
--   - encoding: Definition 1.1 with fresh, independent gate, jump and geometric variables → IsPromotionNoise: one independent draw (U, J, G) per (item, operation index) with law Uniform[0,1] ⊗ μJ ⊗ Geom₀(1−p); reason: the published model of the base mission; realizes the transition probabilities (1)
--   - encoding: every key set, probability space → key type α : Type and sample space Ω : Type; reason: the constants are chosen before these types, which fixes their universe; every concrete instance lives there
--   - encoding: "with probability at least 1 − δ, X ≤ B" → P{X > B} ≤ δ; reason: complement
--   - encoding: Definition 1.6: heights re-initialized at each epoch start, all randomness of an epoch fresh → noise indexed by ((item, epoch), draw) under IsPromotionNoise; heights rsHeight; schedule epochState; reason: realizes Definition 1.6 with independent epochs
--   - encoding: IndepFun / sources / OPT_WB / expectations in part F → as in theorem_F; reason: the same model
--   - encoding: log(1/δ) → natural logarithm; reason: the base only changes the constant
--   - encoding: times t = 1, …, F; f_t = f_{x_t}(t) → 0-based positions t; t + 1 operations so far; f_t = opCount σ x_t t + 1; reason: index shift only
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Theorem 8.3, p.42, with Theorems A–C (pp.7–8), E (p.10), F (p.11); Lemma 8.2, p.41

import Mathlib
import Definitions.Def_SkipListConc_IsPromotionNoise
import Definitions.Def_SkipListConc_Supplement_chargeBench
import Definitions.Def_SkipListConc_Supplement_treeCharge
import Definitions.Def_SkipListConc_Supplement_treeTotalCost
import Definitions.Def_SkipListConc_entropy
import Definitions.Def_SkipListConc_Supplement_benchSum
import Definitions.Def_SkipListConc_Supplement_treeReseededCost
import Definitions.Def_SkipListConc_Supplement_OPTWB
import Definitions.Def_SkipListConc_Supplement_accessList
import Definitions.Def_SkipListConc_Supplement_IsStationarySource
import Definitions.Def_SkipListConc_Supplement_IsPiecewiseStationarySource

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SkipListConc.Supplement

/-- Theorem 8.3 (transfer to trees) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Theorem 8.3, p.42). Theorems A to C, E and F hold for
the self-adjusting treap and the self-adjusting zip tree, with the search cost, and in Theorem F the
cost `cost(X)`, read as the tree cost including restructuring, and with constants larger by the
factor `c_T` of Lemma 8.2. Under reseeding the tree redraws every priority at the start of each
epoch and is rebuilt.

**Formalization Note** Five conjuncts, the statements of Theorems A, B, C, E and F (as in
`theorem_A`, `theorem_B`, the published `SkipListConc.theorem_C`, `theorem_E`, `theorem_F`) with the
skip-list cost replaced by the tree cost: `treeCharge` / `treeTotalCost` (nodes the tree search
visits in the equivalent tree plus ancestors the target moves past, priorities following
Definition 1.1) and, under reseeding, `treeReseededCost` (priorities redrawn per epoch,
Cartesian-tree rebuild of one unit per item present). "Constants larger by `c_T`" leaves every
constant existential, chosen after the same parameters as in the transferred theorem. -/
theorem theorem_8_3 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ K : ℕ, 1 ≤ K →
      ∃ C : ℝ, 0 < C ∧
        ∀ {α : Type} [LinearOrder α] (σ : List α) {Ω : Type} [MeasurableSpace Ω]
          (P : Measure Ω) (μJ : Measure (ℕ → Fin K)) (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ),
          IsPromotionNoise p K μJ P ξ → ∀ t : Fin σ.length,
            (∀ u : ℝ, 0 ≤ u →
              P {ω | C * (chargeBench p σ t + u) < (treeCharge p ξ σ t ω : ℝ)} ≤
                ENNReal.ofReal (3 * Real.exp (-u))) ∧
            ∀ δ : ℝ, 0 < δ → δ < 1 →
              P {ω | C * (1 + Real.logb (1 / p)
                    (((t : ℕ) + 1 : ℝ) / ((opCount σ (σ.get t) t : ℝ) + 1)) + Real.log (1 / δ)) <
                  (treeCharge p ξ σ t ω : ℝ)} ≤ ENNReal.ofReal δ) ∧
    (∀ K : ℕ, 1 ≤ K →
      ∃ C : ℝ, 0 < C ∧
        ∀ {α : Type} [LinearOrder α] (σ : List α) {Ω : Type} [MeasurableSpace Ω]
          (P : Measure Ω) (μJ : Measure (ℕ → Fin K)) (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ),
          IsPromotionNoise p K μJ P ξ → ∀ δ : ℝ, 0 < δ → δ < 1 →
            P {ω | C * (benchSum p σ * (1 + Real.log (1 / δ))) < (treeTotalCost p ξ σ ω : ℝ)} ≤
                ENNReal.ofReal δ ∧
              P {ω | C * (entropy p σ * (1 + Real.log (1 / δ))) < (treeTotalCost p ξ σ ω : ℝ)} ≤
                ENNReal.ofReal δ) ∧
    (∀ K : ℕ, 1 ≤ K →
      ∃ C : ℝ, 0 < C ∧
        ∀ {α : Type} [LinearOrder α] (σ : List α) {Ω : Type} [MeasurableSpace Ω]
          (P : Measure Ω) (μJ : Measure (ℕ → Fin K)) (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ),
          IsPromotionNoise p K μJ P ξ → ∀ δ : ℝ, 0 < δ → δ < 1 →
            P {ω | C * (entropy p σ + (σ.length : ℝ) * Real.log (1 / δ)) <
                (treeTotalCost p ξ σ ω : ℝ)} ≤ ENNReal.ofReal δ) ∧
    (∀ K : ℕ, 1 ≤ K →
      (∃ C : ℝ, 0 < C ∧
        ∀ {α : Type} [LinearOrder α] (σ : List α) {Ω : Type} [MeasurableSpace Ω]
          (P : Measure Ω) (μJ : Measure (ℕ → Fin K))
          (ξ : (α × ℕ) × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ),
          IsPromotionNoise p K μJ P ξ → ∀ δ : ℝ, 0 < δ → δ < 1 →
            P {ω | C * (entropy p σ + (σ.toFinset.card : ℝ) * Real.log (1 / δ)) <
                (treeReseededCost p ξ σ ω : ℝ)} ≤ ENNReal.ofReal δ) ∧
      ∀ κ : ℝ, 0 < κ → ∃ C' : ℝ, 0 < C' ∧
        ∀ {α : Type} [LinearOrder α] (σ : List α) {Ω : Type} [MeasurableSpace Ω]
          (P : Measure Ω) (μJ : Measure (ℕ → Fin K))
          (ξ : (α × ℕ) × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ),
          IsPromotionNoise p K μJ P ξ → 2 ≤ σ.toFinset.card → (∀ x ∈ σ, 2 ≤ σ.count x) →
            P {ω | C' * entropy p σ < (treeReseededCost p ξ σ ω : ℝ)} ≤
              ENNReal.ofReal ((σ.toFinset.card : ℝ) ^ (-κ))) ∧
    (∃ C0 : ℝ, 0 < C0 ∧ ∀ K : ℕ, 1 ≤ K → ∀ B : ℕ, 2 ≤ B → ∃ C : ℝ, 0 < C ∧
      (∀ {α : Type} [LinearOrder α] (ins : List α), ins.Nodup → 2 ≤ ins.length →
        ∀ (m : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μJ : Measure (ℕ → Fin K))
        (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (X : Fin m → Ω → Fin ins.length),
        IsPromotionNoise p K μJ P ξ → IsStationarySource P X →
        IndepFun (fun ω i => X i ω) (fun ω k => ξ k ω) P →
          ∫⁻ ω, (treeTotalCost p ξ (ins ++ accessList ins (fun i => X i ω)) ω : ℝ≥0∞) ∂P ≤
              ENNReal.ofReal C * (∫⁻ ω, ((OPTWB B ins.toFinset (accessList ins (fun i => X i ω))) : ℝ≥0∞) ∂P +
                ENNReal.ofReal ((ins.length : ℝ) * Real.logb 2 ((ins.length : ℝ) + m))) ∧
          ∀ δ : ℝ, 0 < δ → δ < 1 → C0 * Real.logb 2 ((ins.length : ℝ) + m) ^ 2 * Real.log (1 / δ) ≤ m →
            P {ω | C * (1 + Real.log (1 / δ)) * (((OPTWB B ins.toFinset (accessList ins (fun i => X i ω))) : ℝ) + (ins.length : ℝ) * Real.logb 2 ((ins.length : ℝ) + m)) <
                (treeTotalCost p ξ (ins ++ accessList ins (fun i => X i ω)) ω : ℝ)} ≤ ENNReal.ofReal (4 * δ)) ∧
      (∀ {α : Type} [LinearOrder α] (ins : List α), ins.Nodup → 2 ≤ ins.length →
        ∀ (m : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μJ : Measure (ℕ → Fin K))
        (ξ : (α × ℕ) × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (Ph : ℕ) (X : Fin m → Ω → Fin ins.length),
        IsPromotionNoise p K μJ P ξ → IsPiecewiseStationarySource P X Ph →
        IndepFun (fun ω i => X i ω) (fun ω k => ξ k ω) P →
          ∫⁻ ω, (treeReseededCost p ξ (ins ++ accessList ins (fun i => X i ω)) ω : ℝ≥0∞) ∂P ≤
              ENNReal.ofReal C * (∫⁻ ω, ((OPTWB B ins.toFinset (accessList ins (fun i => X i ω))) : ℝ≥0∞) ∂P +
                ENNReal.ofReal ((ins.length : ℝ) * Real.logb 2 ((ins.length : ℝ) + m) +
                  m * Real.logb 2 (1 + (ins.length : ℝ) * Ph / m))) ∧
          ∀ δ : ℝ, 0 < δ → δ < 1 → C0 * Real.logb 2 ((ins.length : ℝ) + m) ^ 2 * Real.log (1 / δ) ≤ m →
            P {ω | C * (((OPTWB B ins.toFinset (accessList ins (fun i => X i ω))) : ℝ) + (ins.length : ℝ) * Real.logb 2 ((ins.length : ℝ) + m) +
                    m * Real.logb 2 (1 + (ins.length : ℝ) * Ph / m) + (ins.length : ℝ) * Real.log (1 / δ)) <
                (treeReseededCost p ξ (ins ++ accessList ins (fun i => X i ω)) ω : ℝ)} ≤ ENNReal.ofReal (3 * δ))) := by sorry

end SkipListConc.Supplement
