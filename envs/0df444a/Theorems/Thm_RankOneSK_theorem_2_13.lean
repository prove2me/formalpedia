-- Prove2me | Theorems.Thm_RankOneSK_theorem_2_13
-- name    : RankOneSK.theorem_2_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:28:49.448672+00:00
-- url     : https://prove2.me/theorems/3d0dcc03-f863-40f6-8a88-393dbc2ce18c
-- title:
--   Theorem 2.13 — Borell–TIS for a separable, not necessarily centered Gaussian process: $P(\sup X-\mathbb E\sup X\ge t)\le e^{-t^2/(8\sigma^2)}$
-- statement:
--   Let $\{X_i\}_{i\in I}$ be a Gaussian process (all finite-dimensional distributions Gaussian, means arbitrary) that is separable, and whose supremum $\sup_{i\in I}X_i$ is almost surely finite, measurable and integrable. Suppose $\sigma>0$ and $\operatorname{Var}X_i\le\sigma^2$ for every $i\in I$.
--
--   **Theorem 2.13** (Borell–TIS; non-centered version). For every $t\ge0$,
--   $$\Pr\Big(\sup_{i\in I}X_i-\mathbb E\Big[\sup_{i\in I}X_i\Big]\ge t\Big)\le\exp\Big(-\frac{t^2}{8\sigma^2}\Big).$$
--
--   It gives the concentration (18) of the supremum over the sphere in the proof of Lemma 2.10.
--
--   **Formalization Note** Separability is encoded as the existence of a countable $D\subseteq I$ with $\sup_{i\in I}X_i=\sup_{i\in D}X_i$ almost surely.
--
--   Differences from the source:
--   - generalization: {X_i} separable → there is a countable D ⊆ I with sup_{i∈I} X_i = sup_{i∈D} X_i almost surely; reason: separability in Doob's sense implies this, so the hypothesis is weaker
--   - encoding: measurable, integrable supremum → sup_i X_i a.s. bounded above and integrable (a.e.-strongly measurable); reason: a measurable integrable real supremum satisfies both; the real-valued supremum needs a.s. finiteness
--   - encoding: Gaussian process, Var X_i → IsGaussianProcess, ProbabilityTheory.variance (X i) P; reason: Mathlib definitions; Gaussian variances are finite
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Theorem 2.13, p.17 (PDF p.18), citing [Bor76, CIS76] and [Sel24]

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RankOneSK

/-- **Theorem 2.13 (Borell–TIS inequality [Bor76, CIS76]; non-centered version [Sel24]).** Let
`{X_i}_{i∈I}` be a separable, not necessarily centered Gaussian process with a measurable, integrable
supremum. Suppose `σ > 0` and `Var X_i ⩽ σ²` for every `i ∈ I`. Then for every `t ⩾ 0`,
`P(sup_{i∈I} X_i − E[sup_{i∈I} X_i] ⩾ t) ⩽ exp(−t²/(8σ²))`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Theorem 2.13, p.17.

**Formalization Note** `I` is an arbitrary index type. Gaussian process is Mathlib's
`IsGaussianProcess`; the means are arbitrary. Separability is encoded as: there is a countable `D ⊆ I`
with `sup_{i∈I} X_i = sup_{i∈D} X_i` almost surely (implied by separability in Doob's sense). "Integrable
supremum" is: a.s. bounded above, and `ω ↦ sup_i X_i(ω)` integrable (which includes a.e.-measurability).
The constant `8` is the one printed. -/
theorem theorem_2_13 {I : Type*} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : I → Ω → ℝ) (hX : IsGaussianProcess X P)
    (hsep : ∃ D : Set I, D.Countable ∧ ∀ᵐ ω ∂P, (⨆ i, X i ω) = ⨆ i : D, X i ω)
    (hbdd : ∀ᵐ ω ∂P, BddAbove (Set.range fun i => X i ω))
    (hint : Integrable (fun ω => ⨆ i, X i ω) P)
    (σ : ℝ) (hσ : 0 < σ) (hvar : ∀ i, variance (X i) P ≤ σ ^ 2) :
    ∀ t : ℝ, 0 ≤ t →
      P {ω | t ≤ (⨆ i, X i ω) - ∫ ω', (⨆ i, X i ω') ∂P} ≤
        ENNReal.ofReal (Real.exp (-(t ^ 2 / (8 * σ ^ 2)))) := by sorry

end RankOneSK
