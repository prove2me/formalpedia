-- Prove2me | Theorems.Thm_StrategicNRM_lemma_4
-- name    : StrategicNRM.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:14.650991+00:00
-- url     : https://prove2.me/theorems/8fa8b2ac-9302-4df6-9369-82d1e9af6beb
-- title:
--   Lemma 4, p.16 (corrected: truncated virtual values, or $v\bar F_j(v)\to0$)
-- statement:
--   Let $\tilde J^1_B$ be the value of problem (11) with the virtual value truncated at $B$. Then:
--
--   (a) with no further condition,
--
--   $$
--   \hat J\le\sup_{B<\infty}\tilde J^1_B ;
--   $$
--
--   (b) if $v\bar F_j(v)\to 0$ as $v\to\infty$ for every $j$, and the virtual value of each product is integrable under its own law, then the printed statement holds:
--
--   $$
--   \hat J\le\tilde J^1 .
--   $$
--
--   Both conditions of (b) hold whenever $E[v^j]<\infty$. This step reduces the payments to virtual values, one product at a time, as Myerson's argument does.
--
--   Differences from the source:
--   - correction: Ĵ ≤ J̃¹ → (a) Ĵ ≤ sup_B J̃¹_B over finite truncations, and (b) Ĵ ≤ J̃¹ if v F̄ⱼ(v) → 0 and the virtual value is integrable; reason: the printed statement is false: for n = 1, F̄(v) = 1/(1+v) the virtual value is −1, so J̃¹ = 0, while a posted price s > 0 with x₀ large is feasible for (7) with revenue λT s/(1+s) > 0; step (17) subtracts two infinite integrals and the true identity carries lim v F̄(v). The integrability in (b) excludes only, under v F̄ⱼ → 0, the case E[ψⱼ⁺] = ∞, where b̃ = 1{ψⱼ > 0, vʲ > M} has objective +∞ and the printed J̃¹ is +∞, so the printed bound is trivial there; it holds whenever E[vʲ] < ∞
--   - reading: E[Σⱼ b̃ʲ_φ] ≤ 1, ∀ φ → Σⱼ b̃ʲ_φ ≤ 1 for every φ; reason: b̃ is a function of φ alone, and the proof of Lemma 6 uses b̃ʲ ≤ χ termwise
--   - encoding: the objective of (11) as an expectation over H_T → λT times the expectation under μ, by Campbell's formula; reason: the two are equal
--   - reading: (7) lists no constraint on τ_φ → τ_φ ∈ [t_φ, T] for every type, and no causality; reason: a variable y_φ of p.11 has τ_φ ∈ [t_φ, T]; (7) does not list causality, so it is not asked
--   - encoding: the objective of (7) as an expectation → an extended real: the expected total of positive parts minus that of negative parts, the latter required finite; reason: a solution with infinite expected negative payments has objective −∞ or undefined and cannot raise the supremum; +∞ must not be read as a Bochner 0; on integrable payments the two agree
--   - encoding: (12) over all b̃ with b̃ʲ_φ ∈ [0,1] → b̃ measurable with Σⱼ ψⱼᴮ(vʲ) b̃ʲ integrable under μ; reason: the objective must be defined; for finite B, ψᴮ f is integrable (ψᴮ ≤ B, and ∫ψ⁻ f ≤ ∫₀ᴮ F̄), and at B = ∞ under Assumption 1 or under the hypotheses of (b) every measurable b̃ ∈ [0,1] qualifies
--   - encoding: a Poisson process of rate λ on [0,T] of customers with i.i.d. marks → a Poisson(λT) number of i.i.d. types with uniform arrival, and E₋φ as integration over a fresh crowd; reason: the two are the same law; removing a point from a Poisson process leaves a Poisson process
-- source:
--   Chen & Trichakis, On Revenue Management with Strategic Customers Choosing When and What to Buy, SSRN 2959489 (version of May 29, 2018), §3.2.2, Lemma 4, p.16

import Mathlib
import Definitions.Def_StrategicNRM_Decoupled
import Definitions.Def_StrategicNRM_Virtual

open MeasureTheory
open scoped ENNReal NNReal

namespace StrategicNRM

variable {n m : ℕ}

/-- Chen & Trichakis, SSRN 2959489 (version of May 29, 2018), Lemma 4, p.16, **corrected**. Printed:
`Ĵ ≤ J̃¹`, which is false without a tail condition (for `F̄(v) = 1/(1+v)` the virtual value is `−1`
and `J̃¹ = 0`, while a posted price earns a positive revenue).

(a) `Ĵ ≤ sup_B J̃¹_B` over the finite truncations of the virtual value, with no condition.

(b) The printed `Ĵ ≤ J̃¹`, if `v F̄ⱼ(v) → 0` as `v → ∞` and the objective of (12) is defined, in
the sense that the virtual value of each product is integrable. -/
theorem lemma_4 (I : Instance n m) :
    Jhat I ≤ ⨆ B : ℝ≥0, I.Jtilde (B : ℝ≥0∞) 1 ∧
      ((∀ j, Filter.Tendsto (fun v => v * I.FbarR j v) Filter.atTop (nhds 0)) →
        (∀ j, Integrable (I.virtualB ⊤ j) (I.valLaw j)) →
        Jhat I ≤ I.Jtilde ⊤ 1) := by sorry

end StrategicNRM
