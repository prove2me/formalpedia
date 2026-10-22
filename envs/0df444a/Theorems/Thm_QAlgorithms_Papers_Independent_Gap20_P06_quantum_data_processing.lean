-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P06_quantum_data_processing
-- name    : QAlgorithms.Papers.Independent.Gap20.P06.quantum_data_processing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:17:01.00346+00:00
-- url     : https://prove2.me/theorems/0fff5c10-65f8-4df8-a06a-45ad66464732
-- title:
--   Quantum data processing: the full coherent-information chain
-- statement:
--   Let $Q$ and $R$ be nonzero finite-dimensional complex Hilbert spaces with fixed coordinate bases, let $\rho$ be a positive semidefinite trace-one operator on $Q$, and let $|\Psi\rangle\in R\otimes Q$ be a unit vector with $\operatorname{Tr}_R|\Psi\rangle\langle\Psi|=\rho$. The reference $R$ is unchanged. Every channel below is completely positive, trace preserving, and linear on all operators. Entropies $S$ are in bits, with $0\log_2 0=0$. For a channel $\Phi$, write $\sigma_{RQ}=(\operatorname{id}_R\otimes\Phi)(|\Psi\rangle\langle\Psi|)$, $S_e(\rho,\Phi)=S(\sigma_{RQ})$, and $I_e(\rho,\Phi)=S(\Phi(\rho))-S_e(\rho,\Phi)$.
--
--   Let $\Phi$ and $\Gamma$ be successive channels on $Q$; the second acts on $Q$ alone, so the total process is $\Gamma\circ\Phi$. Then
--
--   $$
--   S(\rho)\ge I_e(\rho,\Phi)\ge I_e(\rho,\Gamma\circ\Phi).
--   $$
--
--   Both coherent informations use the original input $\rho$ and its original purification. The inequality limits the quantum information retained after additional channel processing.
-- source:
--   Quantum data processing and error correction, arXiv:quant-ph/9604022v1, PDF p. 13, §5, Eq.(5)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P06

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.10--13, Eq.(5): the entire data-processing chain. Both joint entropies
use the original purification; the second stage is a channel on Q alone. -/
theorem quantum_data_processing {R Q : Type*}
    [Fintype R] [Fintype Q] [Nonempty R] [Nonempty Q]
    (rho : Matrix Q Q ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (R × Q)) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = rho)
    (f g : Superop Q Q) (hf : IsChannel f) (hg : IsChannel g) :
    (vnEntropy (f rho) - vnEntropy (idTensorSuperop f (pureDensity psi))) ≤ vnEntropy rho ∧
      (vnEntropy ((g ∘ f) rho) - vnEntropy (idTensorSuperop (g ∘ f) (pureDensity psi))) ≤
        (vnEntropy (f rho) - vnEntropy (idTensorSuperop f (pureDensity psi))) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P06

end
