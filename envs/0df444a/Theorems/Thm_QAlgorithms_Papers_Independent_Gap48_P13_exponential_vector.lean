-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P13_exponential_vector
-- name    : QAlgorithms.Papers.Independent.Gap48.P13.exponential_vector
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:36:59.547272+00:00
-- url     : https://prove2.me/theorems/37712fc2-2b8f-41cb-9bd9-4739b4a655a5
-- title:
--   Exponential Hermite vectors and their norm
-- statement:
--   Let $\phi_n$ be the normalized physicists' Hermite functions in $L^2(\mathbb R,dx)$, and use their complete number-basis representation. For every $z\in\mathbb C$, the Hilbert-space series $e(z)=\sum_{n\ge0}z^n\phi_n/\sqrt{n!}$ converges. At each $x\in\mathbb R$ its pointwise series satisfies
--
--   $$e(z)(x)=\pi^{-1/4}\exp\!\left(-\frac{z^2+x^2}{2}\right)\exp(\sqrt2zx).$$
--
--   The creation-vector series also converges, and
--
--   $$e(z)=\sum_{n\ge0}\frac{z^n}{n!}(a^+)^n\phi_0=\exp(za^+)\phi_0,\qquad \|e(z)\|=\exp(|z|^2/2).$$
--
--   Here $(a^+)^n\phi_0=\sqrt{n!}\phi_n$, and the exponential denotes this vector series. These unnormalized vectors give the generating function of the Hermite basis.
-- source:
--   Markov triplets on CCR-algebras, arXiv:0812.3724v2, PDF p. 4, Lemma 1.1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P13

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

/-- Lemma 1.1, PDF p.4: all three identities, with both Hilbert-series convergence
and pointwise convergence in the Hermite realization; the vector is unnormalized. -/
theorem exponential_vector (z : ℂ) :
    HasSum (fun n : ℕ =>
      (z ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ)) • Osc.fockKet n)
      (exponentialVector z) ∧
    (∀ x : ℝ, HasSum (fun n : ℕ =>
      z ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) * hermiteValue n x)
      ((Real.rpow Real.pi (-(1 : ℝ) / 4) : ℂ) *
        Complex.exp (-(z ^ 2 + (x : ℂ) ^ 2) / 2) *
        Complex.exp (z * (x : ℂ) * (Real.sqrt 2 : ℂ)))) ∧
    HasSum (fun n : ℕ =>
      (z ^ n / (Nat.factorial n : ℂ)) • creationPowerVacuum n)
      (creationExponentialVacuum z) ∧
    exponentialVector z = creationExponentialVacuum z ∧
    ‖exponentialVector z‖ = Real.exp (Complex.normSq z / 2) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P13

end
