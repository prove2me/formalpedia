-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P06_perfect_fidelity_iff_support
-- name    : QAlgorithms.Papers.Independent.Gap20.P06.perfect_fidelity_iff_support
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:17:43.786426+00:00
-- url     : https://prove2.me/theorems/2f4b9fd6-54a4-4133-a975-d3bbd0ec7c71
-- title:
--   Entanglement fidelity one iff all supported pure states have fidelity one
-- statement:
--   Let $Q$ and $R$ be nonzero finite-dimensional complex Hilbert spaces with fixed coordinate bases, let $\rho$ be a positive semidefinite trace-one operator on $Q$, and let $|\Psi\rangle\in R\otimes Q$ be a unit vector with $\operatorname{Tr}_R|\Psi\rangle\langle\Psi|=\rho$. The reference $R$ is unchanged. Every channel below is completely positive, trace preserving, and linear on all operators. Entropies $S$ are in bits, with $0\log_2 0=0$. For a channel $\Phi$, write $\sigma_{RQ}=(\operatorname{id}_R\otimes\Phi)(|\Psi\rangle\langle\Psi|)$, $S_e(\rho,\Phi)=S(\sigma_{RQ})$, and $I_e(\rho,\Phi)=S(\Phi(\rho))-S_e(\rho,\Phi)$.
--
--   Define $F_e(\rho,\Phi)=\langle\Psi|\sigma_{RQ}|\Psi\rangle$ and let $\operatorname{supp}\rho=\operatorname{ran}\rho$. Then
--
--   $$
--   F_e(\rho,\Phi)=1\quad\Longleftrightarrow\quad
--   \forall v\in\operatorname{supp}\rho,\quad \|v\|=1\ \Longrightarrow\
--   \langle v|\Phi(|v\rangle\langle v|)|v\rangle=1.
--   $$
--
--   This connects exact preservation of entanglement to exact preservation of every normalized superposition in the input support, including one-dimensional support.
-- source:
--   Quantum data processing and error correction, arXiv:quant-ph/9604022v1, PDF p. 7, §2, concluding exact fidelity criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P06

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.6--7 (conclusion of Section 2): Fe=1 iff every normalized pure vector
in the support has input-output fidelity one, including every superposition. -/
theorem perfect_fidelity_iff_support {R Q : Type*}
    [Fintype R] [Fintype Q] [Nonempty R] [Nonempty Q]
    (rho : Matrix Q Q ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (R × Q)) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = rho)
    (f : Superop Q Q) (hf : IsChannel f) :
    inputEntanglementFidelity psi f = 1 ↔
      ∀ v : EuclideanSpace ℂ Q, ‖v‖ = 1 → v ∈ LinearMap.range (Matrix.toEuclideanLin rho) →
        effectProb (pureDensity v) (f (pureDensity v)) = 1 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P06

end
