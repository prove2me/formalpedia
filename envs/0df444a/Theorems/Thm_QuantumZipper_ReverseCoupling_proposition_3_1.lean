-- Prove2me | Theorems.Thm_QuantumZipper_ReverseCoupling_proposition_3_1
-- name    : QuantumZipper.ReverseCoupling.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:34.005962+00:00
-- url     : https://prove2.me/theorems/0e439c66-2b5c-4171-8f93-6e8a85cd4351
-- title:
--   Proposition 3.1 (free boundary), p. 42 — the free boundary GFF is the only random modulo-constant distribution with Gaussian one-dimensional marginals of variance (3.6)
-- statement:
--   Let $h$ be a random modulo-additive-constant distribution on $\mathbb H$: each pairing $(h,\rho)$ with a mean-zero $\rho$ is a random variable, and each sample is linear on mean-zero test functions. Suppose that for every $\rho\in H_s(\mathbb H)$ with $\int_{\mathbb H}\rho(z)\,dz=0$,
--   $$(h,\rho)\sim\mathcal N\big(0,\,E(\rho,\rho)\big),$$
--   with $E$ the covariance (3.6). Then $h$ is a free boundary GFF: for all mean-zero $\rho_1,\dots,\rho_n$, the vector $((h,\rho_1),\dots,(h,\rho_n))$ is a centred Gaussian vector with covariance $(E(\rho_i,\rho_j))_{i,j}$.
--
--   This is the step that ends the proof of Theorem 1.2: one checks the one-dimensional laws of the constructed field and concludes that it is the GFF.
--
--   **Formalization Note** "The only" is stated as: the hypothesis forces every finite-dimensional law of the mean-zero pairings to be that of the free boundary GFF. That the GFF has the property is the case $n=1$ of the definition. Continuity of samples in $\rho$ is not assumed (the conclusion holds without it). The first sentence of the proposition (zero boundary GFF, (3.5)) is not stated.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, Proposition 3.1, p. 42 (second sentence)

import Mathlib
import Definitions.Def_QuantumZipper_ReverseCoupling_ZipperFields

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper.ReverseCoupling

/-- **Proposition 3.1** (free boundary part, second sentence), p. 42: "Similarly, the free boundary GFF
is the only random modulo-additive-constant distribution on `ℍ` with the property that for each
`ρ ∈ H_s(ℍ)` with `∫_ℍ ρ(z) dz = 0` the random variable `(h, ρ)` is a mean-zero Gaussian with variance
given by (3.6)."
Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, Proposition 3.1, p. 42.

Let `h : Ω → H_s(ℍ) → ℝ` be a random modulo-additive-constant distribution: each mean-zero pairing `(h, ρ)` is
measurable and each sample is linear on mean-zero test functions. If for every mean-zero `ρ` the law
of `(h, ρ)` is `N(0, E(ρ, ρ))`, then `h` is a free boundary GFF: every finite family of mean-zero
pairings is the centred Gaussian vector with covariance `(E(ρ_i, ρ_j))`.

**Formalization Note** "The only" is stated as: the hypothesis determines all finite-dimensional
laws of the mean-zero pairings, namely those of `IsFreeBoundaryGFF` (that the GFF itself has the
property is the case `n = 1` of the predicate). Continuity of the sample in `ρ` is not assumed; the
statement is true without it, so this is a mild generalization. The zero boundary sentence ((3.5))
is not stated. -/
theorem proposition_3_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → TestFn → ℝ) (hmeas : ∀ ρ : TestFn, MeanZero ρ → Measurable fun ω => h ω ρ)
    (hlin : ∀ ω (a b : ℝ) (ρ σ : TestFn), MeanZero ρ → MeanZero σ →
      h ω (a • ρ + b • σ) = a * h ω ρ + b * h ω σ)
    (hlaw : ∀ ρ : TestFn, MeanZero ρ →
      P.map (fun ω => h ω ρ) = gaussianReal 0 (Real.toNNReal (energy ρ ρ))) :
    IsFreeBoundaryGFF h P := by sorry

end QuantumZipper.ReverseCoupling
