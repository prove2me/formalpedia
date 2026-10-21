-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P41_duplicator_factorization
-- name    : QAlgorithms.Papers.Independent.Renew46.P41.duplicator_factorization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:22:23.954334+00:00
-- url     : https://prove2.me/theorems/1e51070f-6be7-4532-8e8e-399a43892615
-- title:
--   Gain-two amplifier and balanced beam splitter factorize the duplicator
-- statement:
--   On full oscillator modes $(0,1,z)$, there are unitaries $A$ and $B$ with the Heisenberg actions
--
--   $$a_0'=\sqrt2a_0+a_z^\dagger,\qquad a_z'=a_0^\dagger+\sqrt2a_z,\qquad a_0''=(a_0'+a_1)/\sqrt2,\qquad a_1''=(a_0'-a_1)/\sqrt2.$$
--
--   The first unitary is a two-mode phase-insensitive amplifier of power gain 2. The second is the real balanced beam splitter with block $2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ on modes 0 and 1. Their composition has exactly the three-mode canonical action of Eq.(7), as an identity on all Weyl observables. Equivalently, their quadrature matrices multiply to that of Eq.(7), and the two physical gates realize their composite unitary.
--
--   This factorization supplies the optical implementation of the duplicator. Vacuum blank and idler are needed for its coherent-input performance; the operator factorization itself holds for arbitrary inputs and makes no choice of global phase.
-- source:
--   Optimal cloning of coherent states with a linear amplifier and beam splitters, arXiv:quant-ph/0012046v1, PDF p. 2, Eq.(8) and Fig.1

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P41

open scoped BigOperators

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeHilbert ModeOperator Quadrature PhaseVector numberKet IsModeDensity
   FockWeylSystem GaussianMoments unitaryConjugation thermalTensorDensity Symplectic)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, Eq.(8), Fig.1: a gain-two amplifier and a single balanced beam
splitter implement Eq.(7) on every Weyl observable, hence on arbitrary inputs.
Equality of Heisenberg actions avoids choosing an unjustified global phase. -/
theorem duplicator_factorization (W : FockWeylSystem 3) :
    ∃ A B : ModeUnitary 3,
      FockCanonicalAction W A (twoModeAmplifierQuadratures (0 : Fin 3) 2 2) ∧
      FockCanonicalAction W B (modeMixingQuadratures (embeddedOpticalBeam (0 : Fin 3) 1 (Real.pi / 4))) ∧
      modeMixingQuadratures (embeddedOpticalBeam (0 : Fin 3) 1 (Real.pi / 4)) *
        twoModeAmplifierQuadratures (0 : Fin 3) 2 2 = duplicatorMatrix ∧
      OpticalCircuitRealized W [OpticalGate.amplifier 0 2 2,
        OpticalGate.beam 0 1 (Real.pi / 4)] (A.trans B) ∧
      FockCanonicalAction W (A.trans B) duplicatorMatrix := by sorry

end QAlgorithms.Papers.Independent.Renew46.P41

end
