-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P47_logDilationCharacterization
-- name    : QAlgorithms.Papers.Independent.Gap48.P47.logDilationCharacterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:10:01.713688+00:00
-- url     : https://prove2.me/theorems/a228badf-35a7-4e80-8f22-39857c5b65e4
-- title:
--   Local Gaussian dilations and affine CP channels
-- statement:
--   Let $\Phi_A,\Phi_B$ be maps on the trace-class operators of a complete single oscillator. Each is realized by preparing an independent normalized finite-mode Gaussian ancilla, applying a local Gaussian unitary (including translations), and discarding the ancilla, if and only if there exist real local matrices $M_A,G_A,M_B,G_B$ with symmetric $G_j$ and
--   $$
--   G_j+iJ-iM_j^{\mathsf T}JM_j\ge0,\qquad
--   J=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad j\in\{A,B\},
--   $$
--   for which $\Phi_j$ is a completely positive trace-preserving Gaussian channel. More precisely, for some real displacement $d_j$, every actual normalized input density $\tau$ has the convergent Weyl characteristic
--   $$
--   \chi_{\Phi_j(\tau)}(v)=\chi_\tau(M_jv)
--   \exp\!\left(-\frac14v^{\mathsf T}G_jv+i d_j^{\mathsf T}v\right),
--   \qquad \chi_\tau(v)=\operatorname{tr}(\tau e^{iv^{\mathsf T}O}).
--   $$
--   Thus the covariance action is $\Gamma\mapsto M_j^{\mathsf T}\Gamma M_j+G_j$. The channel and its dilation are fixed independently of the input. The local product has block diagonal $M=M_A\oplus M_B$ and $G=G_A\oplus G_B$. Arbitrary finite ancilla counts are allowed.
--
--   This connects the paper's operational LOG class with its affine local CP representation on actual states.
-- source:
--   Conditions for the local manipulation of Gaussian states, arXiv:quant-ph/0109126v2, PDF p. 4, Note [14], Eqs. (2)--(3), Fig. 1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P47

noncomputable section

open scoped BigOperators ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P47

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel GaussianWithCovariance CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue modeCovarianceBlock
   standardFormCovariance)

open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P14 (boundedUnitaryConjugation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1--2, Fig.1, (2)--(3), and p.4 note [14]: local finite-ancilla
Gaussian dilations are exactly the independent affine Gaussian CP channels.
Each local formula holds for ALL input densities. Ancilla counts are arbitrary;
the separate, false single-mode bound in note [14] is not asserted. -/
theorem logDilationCharacterization
    (Phi Psi : DensityKernel 1 → DensityKernel 1) :
    (IsLocalGaussianDilation Phi ∧ IsLocalGaussianDilation Psi) ↔
      ∃ M1 G1 M2 G2 : Cov 1,
        IsAffineLocalGaussian Phi M1 G1 ∧
        IsAffineLocalGaussian Psi M2 G2 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P47

end
