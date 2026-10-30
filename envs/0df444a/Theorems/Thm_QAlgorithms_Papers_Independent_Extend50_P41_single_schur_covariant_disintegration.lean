-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_single_schur_covariant_disintegration
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.single_schur_covariant_disintegration
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:51:07.043779+00:00
-- url     : https://prove2.me/theorems/9f782d0a-3f1b-42d9-891a-9dfd5e289810
-- title:
--   Lemma 4.13: disintegration of a single covariant Schur-factor observable
-- statement:
--   Let $d\ge1$, $N>0$, and let $Y$ be a valid Young diagram with $N$ boxes and at most $d$ rows. Let $\pi_Y$ act on its actual Schur space $H_Y$. Every normalized positive countably additive Borel observable $E$ on the density-state space, covariant under $\pi_Y$, admits a finite positive operator measure $q$ on the ordered simplex with
--   $$E(B)=\int_{U(d)}\pi_Y(U)\,q(\{x:U\operatorname{diag}(x)U^*\in B\})\,\pi_Y(U)^*\,dU$$
--   for every Borel $B$. Haar measure has total mass one; $q(\Sigma)$ is not required to be identity. This is the event form of (111), equivalent to its continuous-test form, and is the single-factor disintegration used in Theorem 4.12.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 22, Lemma 4.13 / (111)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.22-23, Lemma 4.13, (111), in equivalent event form.
Normalization is imposed on E, not on the disintegrating seed q. -/
theorem single_schur_covariant_disintegration {d : ℕ} (hd : 0 < d) (k : ℕ)
    (Y : Schur.Partition d (k+1))
    (E : Measurements.OperatorPOVM (SchurCoordinateIndex Y) (DensityOutcome d))
    (hcov : ∀ (U : Matrix.unitaryGroup (Fin d) ℂ) B, MeasurableSet B →
      E.operator (conjugateState U '' B) = schurAction Y U * E.operator B * star (schurAction Y U)) :
    ∃ q : FiniteOperatorMeasure (SchurCoordinateIndex Y) (OrderedSpectrum d),
      ∀ B : Set (DensityOutcome d), MeasurableSet B → E.operator B = seedObservable Y q B := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
