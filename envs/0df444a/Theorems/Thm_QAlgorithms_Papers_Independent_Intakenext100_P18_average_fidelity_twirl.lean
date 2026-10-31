-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P18_average_fidelity_twirl
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P18.average_fidelity_twirl
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:27:57.292798+00:00
-- url     : https://prove2.me/theorems/ab2137cf-be2d-4bd2-9730-7715935596da
-- title:
--   Haar-average channel fidelity is invariant under twirling
-- statement:
--   Let $d\ge1$ and let $\Lambda$ be a completely positive trace-preserving map. Define $f(\Lambda)=\int\langle\psi|\Lambda(|\psi\rangle\langle\psi|)|\psi\rangle\,d\psi$ using probability Haar measure on unit pure input states, and let $\mathcal T(\Lambda)(X)=\int U^\dagger\Lambda(UXU^\dagger)U\,dU$. Then
--
--   $$f(\Lambda)=f(\mathcal T(\Lambda)).$$
--
--   This is invariance of average squared survival probability. The accepted finite-dimensional CPTP interface supplies integrability without an additional theorem hypothesis.
-- source:
--   General teleportation channel, singlet fraction and quasi-distillation, arXiv:quant-ph/9807091v2, PDF p. 7, §III.D, Lemma 2, eq.(26): average fidelity is invariant under channel twirling

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P18

noncomputable section

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P18

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState teleportWeyl bellKet)

open QAlgorithms.Papers.Independent.Renew46.P40 (initialJoint)

/-- PDF p.7, Lemma 2, (26): normalized Haar-average survival fidelity is
invariant. Integrability is supplied by the accepted CPTP fidelity interface. -/
theorem average_fidelity_twirl (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) :
    QuditFidelity.averageFidelity d hd E =
      QuditFidelity.averageFidelity d hd (QuditFidelity.haarTwirl d hd E) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P18

end
