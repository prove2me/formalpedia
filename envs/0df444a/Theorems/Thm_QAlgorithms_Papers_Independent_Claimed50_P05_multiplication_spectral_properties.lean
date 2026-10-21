-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_multiplication_spectral_properties
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.multiplication_spectral_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:10:28.605693+00:00
-- url     : https://prove2.me/theorems/f67009ac-64d8-4238-91e5-13f5f95436b1
-- title:
--   Corollary 4.6
-- statement:
--   Let $(\Omega,\Sigma,\mu)$ be semifinite, $k\in\{\mathbb R,\mathbb C\}$, and $a\in M(\Omega)$. Write $M_a$ for multiplication on the domain $\{u\in L^2:a u\in L^2\}$, and let $\operatorname{essran}(a)$ be its measure essential range. Then
--
--   $$\sigma(M_a)=\sigma_{\rm ap}(M_a)=\operatorname{essran}(a).$$
--
--   In addition: (a) $M_a$ is injective exactly when $\mu\{a=0\}=0$, and then $M_a^{-1}=M_{a^{-1}}$ on its range; (b) $M_a$ is bounded exactly when $a$ is essentially bounded, and its norm equals $\|a\|_{L^\infty}$; (d) for every $\lambda$ in the resolvent set, $(\lambda I-M_a)^{-1}=M_{(\lambda-a)^{-1}}$; (e) for every measurable $b$, equality $M_a=M_b$ implies $a=b$ $\mu$-almost everywhere; (f) symmetry, self-adjointness, and reality of $a$ almost everywhere are equivalent. The $L^\infty$ norm is represented as an extended nonnegative essential supremum; under boundedness it is finite.
--
--   This records the full spectral description of multiplication operators.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 18, Corollary 4.6

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Corollary 4.6, PDF p.18: all six multiplication-operator conclusions. -/
theorem multiplication_spectral_properties (mu : Measure X) (hmu : Semifinite mu) (a : Symbol X k) :
    ((InjectiveOperator (multiplication mu a) ↔ mu {x | a.val x = 0} = 0) ∧
      (InjectiveOperator (multiplication mu a) → inverse (multiplication mu a) = multiplication mu (reciprocal a))) ∧
    ((BoundedOperator (k := k) (multiplication mu a) ↔ EssentiallyBounded mu a) ∧
      (∀ T : Lp k 2 mu →L[k] Lp k 2 mu, multiplication mu a = boundedGraph T →
        ENNReal.ofReal ‖T‖ = essentialNorm mu a)) ∧
    (spectrumOf (k := k) (multiplication mu a) = approximateSpectrum (k := k) (multiplication mu a) ∧
      approximateSpectrum (k := k) (multiplication mu a) = measureEssentialRange mu a) ∧
    (∀ z, z ∈ resolventSet (k := k) (multiplication mu a) →
      inverse (resolventShift z (multiplication mu a)) = multiplication mu (reciprocal (plus (constant z) (scalar (-1) a)))) ∧
    (∀ b : Symbol X k, multiplication mu a = multiplication mu b → ∀ᵐ x ∂mu, a.val x = b.val x) ∧
    ((Symmetric (k := k) (multiplication mu a) ↔ SelfAdjoint (k := k) (multiplication mu a)) ∧
      (SelfAdjoint (k := k) (multiplication mu a) ↔ ∀ᵐ x ∂mu, star (a.val x) = a.val x)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
