-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P16_haar_average
-- name    : QAlgorithms.Papers.Independent.Support21.P16.haar_average
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:44:47.606602+00:00
-- url     : https://prove2.me/theorems/69bc4e55-165f-413d-b6f4-7c69b682ba8d
-- title:
--   Haar averaging preserves admissibility and improves fidelity
-- statement:
--   Let $d>0$ and $1\le N<M$ be integers, and let $T$ be any complex-linear completely positive trace-preserving map from the $N$-particle Bose input algebra to the full $M$-particle algebra, canonically zero-extended. Let $\mu$ be the Borel Haar probability measure on $U(d)$. Define the entrywise integral
--   $$
--   \overline T(A)=\int_{U(d)}U^{*\otimes M}\,
--   T(U^{\otimes N}AU^{*\otimes N})\,U^{\otimes M}\,d\mu(U).
--   $$
--   Every matrix-entry integrand is integrable. The average is admissible and covariant, and $\overline T=T$ if and only if $T$ is covariant, where covariance means $T(U^{\otimes N}AU^{*\otimes N})=U^{\otimes M}T(A)U^{*\otimes M}$ for all $U,A$. For the worst-case normalized pure-input global overlap $\mathcal F$,
--   $$
--   \mathcal F(\overline T)\ge\mathcal F(T).
--   $$
--   In particular, $\mathcal F(T)=\widehat F$ implies $\mathcal F(\overline T)=\widehat F$, where $\widehat F$ is the supremum over admissible maps.
--
--   This makes the source's symmetrization available for arbitrary competitors; integrability and covariance are conclusions.
-- source:
--   Optimal Cloning of Pure States, arXiv:quant-ph/9804001v1, PDF p. 9, haar-average

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support21.P16

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector powerVector IsCloningCovariant haarAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Support21.P16.unitaryMeasurable

/-- PDF p.9 Eq.(4.2) and its following proof: normalized Haar averaging is
integrable, admissible and covariant, fixes exactly covariant maps, improves
worst-case fidelity, and preserves optimality. The printed 'positive'
F-hat minus overlap has the wrong sign; no such sign assertion is used. -/
theorem haar_average (d N M : ℕ) (hd : 0 < d) (hN : 1 ≤ N) (hNM : N < M)
    (mu : Measure (UnitaryGroup d)) [Measure.IsHaarMeasure mu] [IsProbabilityMeasure mu]
    (T : CloneMap d N M) (hT : IsBoseInputChannel T) :
    (∀ A x y, Integrable (fun u : UnitaryGroup d => rotatedCloner u T A x y) mu) ∧
    IsBoseInputChannel (haarAverage mu T) ∧ IsCloningCovariant (haarAverage mu T) ∧
    (haarAverage mu T = T ↔ IsCloningCovariant T) ∧
    cloningFidelity T ≤ cloningFidelity (haarAverage mu T) ∧
    (cloningFidelity T = optimalFidelity d N M →
      cloningFidelity (haarAverage mu T) = optimalFidelity d N M) := by sorry

end QAlgorithms.Papers.Independent.Support21.P16

end
