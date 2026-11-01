-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P92_localInvariants
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P92.localInvariants
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:35:09.249052+00:00
-- url     : https://prove2.me/theorems/be1e294b-8228-4e88-a53e-d484365a0ec6
-- title:
--   Four local symplectic invariants and the determinant identity
-- statement:
--   Let $V=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$ be a real symmetric $4\times4$ matrix, with $2\times2$ blocks in interleaved mode order. Put $J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ and
--
--   $$
--   I_1=\det A,\quad I_2=\det B,\quad I_3=\det C,\quad I_4=\operatorname{tr}(AJCJBJC^TJ).
--   $$
--
--   For any real $2\times2$ matrices $S_1,S_2$ satisfying $S_jJS_j^T=J$, all four $I_k$ are unchanged by $V\mapsto(S_1\oplus S_2)V(S_1\oplus S_2)^T$. Moreover $\det V=I_1I_2+I_3^2-I_4$. These algebraic identities require symmetry but no Gaussian or positivity assumption.
-- source:
--   Peres-Horodecki separability criterion for continuous variable systems, arXiv:quant-ph/9909044v1, PDF p. 4, PDF pp.3–4: four local symplectic invariants and determinant identity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P92

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsSeparable IsBarycenter)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open QAlgorithms.Papers.Independent.Advance50.P48
  (TwoKernel GaussianTwo IsDiscordCovariance characteristicTwo
   covarianceModeBlock totalPhotonEnergy)

open QAlgorithms.Papers.Independent.Frontier30.P04 (modePhase Covariance twoModeStandard)

open QAlgorithms.Papers.Independent.Claimed50.P30 (canonicalOmega)

open QAlgorithms.Papers.Independent.Gap48.P47 (localSymplecticMatrix)

open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel unitaryCoeff)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3--4, (15)--(16): four local invariants and the determinant identity.
Symmetry is explicit; no Gaussian or positivity assumption is needed for this algebra. -/
theorem localInvariants (V : Covariance 2) (hsymm : V.IsSymm)
    (S1 S2 : LocalMatrix) (hS1 : LocalSymplectic S1) (hS2 : LocalSymplectic S2) :
    (∀ k : Fin 4, simonInvariant (localCovarianceAction V S1 S2) k = simonInvariant V k) ∧
    V.det = simonInvariant V 0 * simonInvariant V 1 +
      simonInvariant V 2 ^ 2 - simonInvariant V 3 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P92

end
