-- Prove2me | Theorems.Thm_ReplicableOL_lemma_3_5
-- name    : ReplicableOL.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:42.609193+00:00
-- url     : https://prove2.me/theorems/226cb38f-c4d6-4ae9-a780-eceaeb69b108
-- title:
--   Lemma 3.5 — lower tail from the fourth moment
-- statement:
--   Let $W$ be a random variable with $\mathbb EW=A>0$ and $\|W\|_4<\infty$, and let $c'\in[0,1)$. Then
--   $$
--   \mathbb P[W\ge c'A]\ge\big((1-c')A/\|W\|_4\big)^{4/3}.
--   $$
--   In particular, in the regime, for every learner satisfying (H2) and every seed value,
--   $$
--   \mathbb P[\widetilde W\ge c'A]\ge(0.4556/1.5265)^{4/3}(1-c')^{4/3}\ge0.1994(1-c')^{4/3}.
--   $$
--   This supplies the probability $1/6$ of the main theorem: it is a one-sided moment inequality that needs no anti-concentration.
--
--   Differences from the source:
--   - encoding: "a random variable" with $\|W\|_4<\infty$ → `Measurable W` and `MemLp W 4 P`, with $\|W\|_4$ as `(eLpNorm W 4 P).toReal`; reason: Lean's forms of the same conditions
--   - encoding: $\widetilde W$ for a learner at a seed, under Construction C → `Wtilde Δ (𝓛.toEpochRule L r)` under `E1`, with $A$ as `advantage T L Δ`; reason: the explicit form on bits; `lemma_3_3` identifies the forms of $A$
--   - encoding: a learner whose maps $a_t$ read $[0,1]$-valued losses → `Learner` with maps on all real loss vectors (`Fin t → Fin 2 → ℝ`); reason: a learner on $[0,1]$ extends measurably to $\mathbb R$ and a `Learner` restricts to $[0,1]$; every law and every `embed` sequence here is carried by $[0,1]^2$
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma 3.5, p.12

import Mathlib
import Definitions.Def_ReplicableOL_Learner
import Definitions.Def_ReplicableOL_advantage
import Definitions.Def_ReplicableOL_Learner_toEpochRule
import Definitions.Def_ReplicableOL_E1
import Definitions.Def_ReplicableOL_Wtilde
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Lemma 3.5.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma 3.5, p.12. The general bound and the "in particular" clause.

**Formalization Note.** `‖W‖₄` is `(eLpNorm W 4 P).toReal`. The second conjunct is for a learner's `W̃` at a fixed seed, under `E1`, in the regime, with `A = advantage T L Δ`. -/
theorem lemma_3_5 {Ω R : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace R] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    (∀ (W : Ω → ℝ) (A c' : ℝ), Measurable W → MemLp W 4 P → ∫ ω, W ω ∂P = A → 0 < A →
      c' ∈ Set.Ico (0 : ℝ) 1 →
      ((1 - c') * A / (eLpNorm W 4 P).toReal) ^ (4 / 3 : ℝ) ≤ P.real {ω | c' * A ≤ W ω}) ∧
    (∀ {T L : ℕ} {Δ c' : ℝ} (𝓛 : Learner 2 T R) (r : R), 0 < Δ → Δ ≤ 1 / 4 → 100 ≤ T / L → 100 ≤ Δ * √(L : ℝ) →
      c' ∈ Set.Ico (0 : ℝ) 1 →
      (0.4556 / 1.5265 : ℝ) ^ (4 / 3 : ℝ) * (1 - c') ^ (4 / 3 : ℝ) ≤
        E1 Δ (fun θ S => if c' * advantage T L Δ ≤ Wtilde Δ (𝓛.toEpochRule L r) θ S then 1 else 0) ∧
      0.1994 * (1 - c') ^ (4 / 3 : ℝ) ≤ (0.4556 / 1.5265 : ℝ) ^ (4 / 3 : ℝ) * (1 - c') ^ (4 / 3 : ℝ)) := by sorry

end ReplicableOL
