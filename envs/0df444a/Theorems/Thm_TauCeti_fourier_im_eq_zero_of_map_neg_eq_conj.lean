-- Prove2me | Theorems.Thm_TauCeti_fourier_im_eq_zero_of_map_neg_eq_conj
-- name    : TauCeti.fourier_im_eq_zero_of_map_neg_eq_conj
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:46:26.032967+00:00
-- url     : https://prove2.me/theorems/e071c4af-7324-4dc6-b0e0-0cdc5b543838
-- title:
--   Conjugate symmetry gives a real Fourier transform
-- statement:
--   Let $V$ be a finite-dimensional real inner-product space with its standard additive Haar measure. Let $F:V\to\mathbb C$ be integrable and satisfy $F(-v)=\overline{F(v)}$ for every $v$. Its Fourier transform satisfies
--
--   $$
--   \operatorname{Im}\widehat F(\xi)=0\qquad(\xi\in V).
--   $$
--
--   Conjugate symmetry of a function thus gives real-valued Fourier data.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/Bochner/Fourier/Nonneg.lean#L601-L632), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/Bochner/Fourier/Nonneg.lean#L601-L632

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.UniformApproximation

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Nonnegativity of the Fourier transform of a positive-definite function

For a continuous, integrable function `F : V → ℂ` on a finite-dimensional real inner-product
space whose subtraction kernel `(a, b) ↦ F (a - b)` is positive definite, the Fourier transform
`𝓕 F` is real and nonnegative: its real part is nonnegative at every frequency and its imaginary
part vanishes. This is the analytic half of Bochner's theorem.

The real-part nonnegativity is proved by Fejér ball averaging. For a fixed frequency `ξ`, the
twisted function `ψ = fourierAtom ξ * F` is still positive definite (Schur product with the
Fourier atom kernel), continuous, and integrable, and `𝓕 F ξ = ∫ ψ`. For `R > 0` the averaged
double integral `J_R = vol(B_R)⁻¹ ∬_{B_R × B_R} ψ (x - y)` has nonnegative real part because it
is a limit of positive-definite double sums (simple-function approximation of the identity),
while Fubini rewrites `J_R = ∫ ψ · overlapRatio R` whose dominated limit as `R → ∞` is `∫ ψ`.

Building on this, the Fourier transform of such a function is itself *integrable*: testing
against a shrinking family of Gaussians and using the Parseval/Fubini identity bounds
`∫ (𝓕 F) · exp (-t‖·‖²)` by `(F 0).re` uniformly in `t`, and Fatou's lemma passes to the limit.

Adapted (Apache 2.0) from the Bochner–Minlos formalization by Michael R. Douglas
(https://github.com/mrdouglasny/bochner, revision `08eb302`), source files `Bochner/FejerPD.lean`
and `Bochner/Main.lean`; the arguments are ported with the positive-definiteness hypotheses
restated through `Matrix.PosSemidef`.

## Main declarations

* `TauCeti.fourier_re_nonneg_of_posSemidef`: the Fourier transform of a
  continuous integrable positive-definite function has nonnegative real part.
* `TauCeti.fourier_im_eq_zero_of_map_neg_eq_conj` and
  `TauCeti.fourier_eq_re_of_map_neg_eq_conj`: for an integrable *conjugate-symmetric* `F`
  (continuity is not needed), the imaginary part of `𝓕 F` vanishes and `𝓕 F` equals its own real
  part; `TauCeti.fourier_im_eq_zero_of_posSemidef` and
  `TauCeti.fourier_eq_re_of_posSemidef` are the positive-definite specializations.
* `TauCeti.integrable_fourier_of_posSemidef`: the Fourier transform of a
  continuous integrable positive-definite function is integrable.
* `TauCeti.fourierInv_re_nonneg_of_posSemidef`,
  `TauCeti.fourierInv_eq_re_of_posSemidef`,
  `TauCeti.integrable_fourierInv_of_posSemidef` and
  `TauCeti.measurable_ofReal_re_fourierInv`: the same facts for the inverse transform `𝓕⁻ F`,
  which is the density of the representing measure of Bochner's theorem.

## References

* W. Rudin, *Fourier Analysis on Groups* (1962), Theorem 1.4.3.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, §4.2, Lemma 4.8.
* Roadmap: TauCetiRoadmap/OneParameterSemigroups/README.md, Part C (Bochner milestone).
-/

 section

open Complex ComplexConjugate Filter MeasureTheory
open scoped ComplexOrder FourierTransform Topology

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

/-! ### A simple-function expansion for integrals of compositions -/

section SimpleFuncExpansion

variable {α : Type*} [MeasurableSpace α]







end SimpleFuncExpansion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-! ### Consequences of positive definiteness for a subtraction kernel -/

section KernelConsequences

variable {ψ : V → ℂ}



end KernelConsequences

/-! ### Step A: the positive-definite double integral has nonnegative real part -/







/-! ### The Fejér overlap ratio -/















/-! ### Step B: the Fubini identity for the Fejér average -/













/-! ### Step C: the integral of a positive-definite function has nonnegative real part -/





/-! ### The main theorems -/

theorem TauCeti.fourier_im_eq_zero_of_map_neg_eq_conj (F : V → ℂ)
    (hsymm : ∀ v : V, F (-v) = conj (F v)) (_hint : _root_.MeasureTheory.Integrable F) (ξ : V) :
    (𝓕 F ξ).im = 0 := by sorry
