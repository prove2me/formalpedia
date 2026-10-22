-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P38_lemma5_coherentDecoder
-- name    : QAlgorithms.Papers.Independent.Gap48.P38.lemma5_coherentDecoder
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:07:15.769181+00:00
-- url     : https://prove2.me/theorems/b66da5d1-75ff-4768-b710-56fd6c7ee606
-- title:
--   Lemma 5: coherent implementation of a decoding measurement
-- statement:
--   Let $|\psi\rangle^{XY}$ be a unit vector on nonempty finite complex registers. Let $\kappa\ge1$, let $U_k$ be $\kappa$ unitaries on $X$, put $|\psi_k\rangle=(U_k\otimes I_Y)|\psi\rangle$, and let $|\psi'_k\rangle^{XY}$ be any unit vectors. Let $\{\Lambda_k\}$ be a POVM on $X$. Define the average measurement error and squared pure-state fidelity by
--
--   $$P=1-\frac1\kappa\sum_k\operatorname{Tr}(\Lambda_k\psi_k^X),\qquad F=\frac1\kappa\sum_k|\langle\psi_k|\psi'_k\rangle|^2.$$
--
--   There are complex phases $\alpha_k$ of modulus one such that the explicitly constructed map
--
--   $$L=\sum_k(\alpha_kU_k^\dagger\sqrt{\Lambda_k})\otimes|k\rangle^K$$
--
--   is an isometry from $X$ to $XK$. Each amplitude $\langle k|\langle\psi|(L\otimes I_Y)|\psi'_k\rangle$ can be taken real and nonnegative, and
--
--   $$\frac1\kappa\sum_k\langle k|\langle\psi|(L\otimes I_Y)|\psi'_k\rangle\ge1-2\bigl(P+\sqrt{1-F}\bigr).$$
--
--   This turns a decoding measurement into coherent communication while retaining the reference $Y$. The real, nonnegative amplitude convention is the one explicitly chosen in the appendix proof.
-- source:
--   Optimal quantum source coding with quantum information at the encoder and decoder, arXiv:0706.2907v2, PDF p. 7, Lemma 5: coherent implementation of a decoding measurement

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Gap48.P38

/-- Lemma 5 (coherent implementation of a decoding measurement), PDF p.7,
proof p.12. The phases make each overlap real and nonnegative, interpreting the
printed complex inequality exactly as its proof does; L is constructed, not assumed. -/
theorem lemma5_coherentDecoder
    (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    [Nonempty X] [Nonempty Y]
    (k : ℕ) (hk : 0 < k) (psi : EuclideanSpace ℂ (X × Y)) (hpsi : ‖psi‖ = 1)
    (U : Fin k → Matrix.unitaryGroup X ℂ)
    (psiPrime : Fin k → EuclideanSpace ℂ (X × Y))
    (hpsiPrime : ∀ j, ‖psiPrime j‖ = 1)
    (Lambda : Fin k → Matrix X X ℂ) (hLambda : IsPOVM Lambda) :
    ∃ alpha : Fin k → ℂ, (∀ j, ‖alpha j‖ = 1) ∧
      let L := coherentDecoder alpha U Lambda
      Lᴴ * L = 1 ∧
      (∀ j, (decoderOverlap psi L (psiPrime j) j).im = 0 ∧
        0 ≤ (decoderOverlap psi L (psiPrime j) j).re) ∧
      (k : ℝ)⁻¹ * ∑ j, (decoderOverlap psi L (psiPrime j) j).re ≥
        1 - 2 * (coherentMeasurementError psi U Lambda +
          Real.sqrt (1 - decodingFidelity psi U psiPrime)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P38

end
