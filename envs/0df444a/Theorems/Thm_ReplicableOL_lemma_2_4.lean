-- Prove2me | Theorems.Thm_ReplicableOL_lemma_2_4
-- name    : ReplicableOL.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:46:54.846453+00:00
-- url     : https://prove2.me/theorems/2db0ed2d-38fa-4705-a027-186e92f4c3e8
-- title:
--   Lemma 2.4 — gain-weighted coin lemma
-- statement:
--   Let $\mu\sim U[-\Delta,\Delta]$ with $\Delta\le\frac14$. Given $\mu$, let $S,S'$ be independent with law $\mathrm{Bern}(\frac12+\mu)^{\otimes L}$. Let $\mathcal G$ be a $\sigma$-field independent of $(\mu,S,S')$, and let $p(s,\cdot)\in[0,1]$ be $\mathcal G$-measurable for each $s$. Put $d:=\mathbb E[|p(S)-p(S')|\mid\mathcal G]$. If $\Delta\sqrt L\ge\sqrt3/8$, then almost surely
--   $$
--   \big|\mathbb E[\mu\,p(S)\mid\mathcal G]\big|\le C_B\Delta^2\sqrt L\cdot d,\qquad \mathrm{Var}(p(S)\mid\mathcal G)\le C_B\Delta\sqrt L\cdot d,\qquad C_B=\frac{32}{3\sqrt3}.
--   $$
--   Without the regime condition, these hold with the factors $\frac43\Delta\max\{1,\frac8{\sqrt3}\Delta\sqrt L\}$ and $\max\{\frac43,C_B\Delta\sqrt L\}$.
--
--   No causality, monotonicity or replicability of $p$ is assumed. The bound is linear in the disagreement, with no logarithm, which is what lets Theorem 2 sum it over epochs.
--
--   Differences from the source:
--   - encoding: $p(s,\cdot)$ jointly measurable and $\mathcal G$-measurable for each $s$ → `Measurable[𝒢] (p s)` for each of the finitely many $s$; reason: on a finite set of blocks this is the joint measurability
--   - encoding: $\mu\sim U[-\Delta,\Delta]$ and $S,S'$ conditionally i.i.d. given $\mu$ → the mass of every rectangle $B\times\{s\}\times\{s'\}$, with $\Delta>0$; reason: these rectangles determine the joint law
--   - encoding: a $\sigma$-field $\mathcal G$ → a sub-$\sigma$-algebra, `h𝒢 : 𝒢 ≤ mΩ`; reason: the conditional expectations of the page are given a sub-$\sigma$-field; Mathlib's `condExp` is $0$ otherwise
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma 2.4, p.8

import Mathlib
import Definitions.Def_ReplicableOL_uniformPrior
import Definitions.Def_ReplicableOL_Block
import Definitions.Def_ReplicableOL_blockWeight
import Definitions.Def_ReplicableOL_CB
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Lemma 2.4.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma 2.4, p.8. Both displayed bounds in the regime, and both bounds with the printed factors without the regime condition ("Without the regime condition, (i) and (ii) hold with the factors …", p.8).

**Formalization Note.** `𝒢` is a sub-σ-algebra (`h𝒢 : 𝒢 ≤ mΩ`, which Mathlib's `condExp` needs). The joint law of `(μ, S, S')` is given by the mass of the rectangles `B × {s} × {s'}`. The rule is `p : Block L → Ω → ℝ`, `𝒢`-measurable for each of the finitely many blocks, which is its joint measurability. Conditional variance is Mathlib's `condVar`. -/
theorem lemma_2_4 {Ω : Type*} (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {L : ℕ} {Δ : ℝ} (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1 / 4)
    (μ : Ω → ℝ) (S S' : Ω → Block L) (hμ : Measurable μ) (hS : Measurable S) (hS' : Measurable S')
    (hlaw : ∀ (B : Set ℝ) (s s' : Block L), MeasurableSet B →
      P {ω | μ ω ∈ B ∧ S ω = s ∧ S' ω = s'} =
        ENNReal.ofReal (∫ x in B, blockWeight x s * blockWeight x s' ∂(uniformPrior Δ)))
    (hindep : Indep 𝒢 (MeasurableSpace.comap (fun ω => (μ ω, S ω, S' ω)) inferInstance) P)
    (p : Block L → Ω → ℝ) (hp : ∀ s, Measurable[𝒢] (p s)) (hp01 : ∀ s ω, p s ω ∈ Set.Icc (0 : ℝ) 1) :
    (√3 / 8 ≤ Δ * √(L : ℝ) →
      (∀ᵐ ω ∂P, |(P[fun ω => μ ω * p (S ω) ω | 𝒢]) ω| ≤
        CB * Δ ^ 2 * √(L : ℝ) * (P[fun ω => |p (S ω) ω - p (S' ω) ω| | 𝒢]) ω) ∧
      (∀ᵐ ω ∂P, (Var[fun ω => p (S ω) ω; P | 𝒢]) ω ≤
        CB * Δ * √(L : ℝ) * (P[fun ω => |p (S ω) ω - p (S' ω) ω| | 𝒢]) ω)) ∧
    (∀ᵐ ω ∂P, |(P[fun ω => μ ω * p (S ω) ω | 𝒢]) ω| ≤
      4 / 3 * Δ * max 1 (8 / √3 * Δ * √(L : ℝ)) * (P[fun ω => |p (S ω) ω - p (S' ω) ω| | 𝒢]) ω) ∧
    (∀ᵐ ω ∂P, (Var[fun ω => p (S ω) ω; P | 𝒢]) ω ≤
      max (4 / 3) (CB * Δ * √(L : ℝ)) * (P[fun ω => |p (S ω) ω - p (S' ω) ω| | 𝒢]) ω) := by sorry

end ReplicableOL
