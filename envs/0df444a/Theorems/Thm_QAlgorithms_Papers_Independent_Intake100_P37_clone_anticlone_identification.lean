-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P37_clone_anticlone_identification
-- name    : QAlgorithms.Papers.Independent.Intake100.P37.clone_anticlone_identification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:07:18.352799+00:00
-- url     : https://prove2.me/theorems/aec8baef-f31f-45a0-91d6-f084d643211e
-- title:
--   Physical clones and ground-state anti-clones
-- statement:
--   Let $A\ge l\ge0$, $m\ge1$, and let $\psi$ be a normalized qubit polarization. Apply the explicit physical readout to $F_l(\psi)$: undo the atomic occupation embedding, perform the fixed ground relabeling, retain the pump outcome $A-l$, and map the photon and ground-state occupations to their normalized symmetric qubit states. If $Q_{m,l}(\psi)$ is the accepted joint cloning/NOT output of [9] with $\theta\psi=(\overline{\psi_1},-\overline{\psi_0})$, then
--
--   $$
--   \mathcal R_lF_l(\psi)=(-1)^lQ_{m,l}(\psi).
--   $$
--
--   Every one of the $M=m+l$ photon-qubit marginals is $\eta|\psi\rangle\langle\psi|+(1-\eta)I_2/2$, where $\eta=m(M+2)/(M(m+2))$. Every one of the $l$ ground-state anti-clone marginals is
--
--   $$
--   \rho_{\rm anti}=\frac{m}{m+2}(I_2-|\psi\rangle\langle\psi|)+\frac1{m+2}I_2.
--   $$
--
--   These are the optimal cloning and universal-NOT marginals identified in the source. The explicit phase preserves the accepted antiunitary convention; the densities agree. No product structure is asserted for the anti-clones, and for $l=0$ there is no anti-clone to sample.
-- source:
--   Lambda's, V's and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, PDF p. 5, Sec. II C, following Eq.(19)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P37

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.5-6: identification with [9], including the branch phase (-1)^l
from the accepted theta convention. Clone and anti-clone marginals are physical
readouts; no tensor-product claim is made about the anti-clones. -/
theorem clone_anticlone_identification (A m l : ℕ) (hm : 1 ≤ m) (hlA : l ≤ A)
    (psi : EuclideanSpace ℂ (Fin 2)) (hpsi : IsState psi) :
    applyMatrix (physicalReadout A m l) (physicalSector A m l psi) =
      (-1 : ℂ) ^ l • QAlgorithms.Papers.Independent.Support21.P18.quantumOutput m l psi ∧
    (∀ k : Fin (m + l),
      QAlgorithms.Papers.Independent.Support21.P18.siteReduction (traceRight (pureDensity
        (applyMatrix (physicalReadout A m l) (physicalSector A m l psi)))) k =
        QAlgorithms.Papers.Independent.Support21.P18.cloneOutput m l psi) ∧
    (∀ k : Fin l,
      QAlgorithms.Papers.Independent.Support21.P18.siteReduction (traceLeft (pureDensity
        (applyMatrix (physicalReadout A m l) (physicalSector A m l psi)))) k =
        QAlgorithms.Papers.Independent.Support21.P18.complementOutput m psi) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P37

end
