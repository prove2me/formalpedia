-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P06_coherentInformation_bound_and_equality
-- name    : QAlgorithms.Papers.Independent.Gap20.P06.coherentInformation_bound_and_equality
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:16:11.35297+00:00
-- url     : https://prove2.me/theorems/722db4a5-fbc8-4fa2-9eb3-3248baeac822
-- title:
--   Coherent information bound and environment factorization criterion
-- statement:
--   Let $Q$ and $R$ be nonzero finite-dimensional complex Hilbert spaces with fixed coordinate bases, let $\rho$ be a positive semidefinite trace-one operator on $Q$, and let $|\Psi\rangle\in R\otimes Q$ be a unit vector with $\operatorname{Tr}_R|\Psi\rangle\langle\Psi|=\rho$. The reference $R$ is unchanged. Every channel below is completely positive, trace preserving, and linear on all operators. Entropies $S$ are in bits, with $0\log_2 0=0$. For a channel $\Phi$, write $\sigma_{RQ}=(\operatorname{id}_R\otimes\Phi)(|\Psi\rangle\langle\Psi|)$, $S_e(\rho,\Phi)=S(\sigma_{RQ})$, and $I_e(\rho,\Phi)=S(\Phi(\rho))-S_e(\rho,\Phi)$.
--
--   Fix any finite nonzero environment $E$, unit vector $|\eta\rangle\in E$, and unitary $U$ on $Q\otimes E$ realizing $\Phi(X)=\operatorname{Tr}_E[U(X\otimes|\eta\rangle\langle\eta|)U^\dagger]$ for every operator $X$. Put $|\Omega\rangle=(I_R\otimes U)(|\Psi\rangle\otimes|\eta\rangle)$, $\sigma_{RE}=\operatorname{Tr}_Q|\Omega\rangle\langle\Omega|$, $\sigma_E=\operatorname{Tr}_Q[U(\rho\otimes|\eta\rangle\langle\eta|)U^\dagger]$, and $\rho_R=\operatorname{Tr}_Q|\Psi\rangle\langle\Psi|$.
--
--   Then
--
--   $$
--   I_e(\rho,\Phi)\le S(\rho),\qquad
--   I_e(\rho,\Phi)=S(\rho)\ \Longleftrightarrow\ \sigma_{RE}=\rho_R\otimes\sigma_E.
--   $$
--
--   The equality criterion identifies lossless coherent information with decoupling of the isolated reference and the initially pure dilation environment.
-- source:
--   Quantum data processing and error correction, arXiv:quant-ph/9604022v1, PDF p. 10, §4, Eq.(4) and equality criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P06

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.9--10, Eq.(4) and the following iff: the coherent-information bound and
its equality criterion for an arbitrary fixed initially pure unitary dilation. -/
theorem coherentInformation_bound_and_equality {R Q E : Type*}
    [Fintype R] [Fintype Q] [Fintype E] [Nonempty R] [Nonempty Q] [Nonempty E]
    (rho : Matrix Q Q ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (R × Q)) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = rho)
    (f : Superop Q Q) (hf : IsChannel f)
    (U : Matrix.unitaryGroup (Q × E) ℂ) (eta : EuclideanSpace ℂ E)
    (heta : ‖eta‖ = 1) (hdil : ∀ X, f X = dilationChannel U eta X) :
    (vnEntropy (f rho) - vnEntropy (idTensorSuperop f (pureDensity psi))) ≤ vnEntropy rho ∧
      ((vnEntropy (f rho) - vnEntropy (idTensorSuperop f (pureDensity psi))) = vnEntropy rho ↔
        referenceEnvironment U eta psi =
          Matrix.kronecker (traceRight (pureDensity psi)) (environmentOutput U eta rho)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P06

end
