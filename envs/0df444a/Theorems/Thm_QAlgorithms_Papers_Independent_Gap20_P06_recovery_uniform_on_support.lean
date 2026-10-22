-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P06_recovery_uniform_on_support
-- name    : QAlgorithms.Papers.Independent.Gap20.P06.recovery_uniform_on_support
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:18:52.210736+00:00
-- url     : https://prove2.me/theorems/ddd40a11-24fe-4d39-9c42-a2bb6c7298d0
-- title:
--   One recovery channel works throughout the original support
-- statement:
--   Let $Q$ and $R$ be nonzero finite-dimensional complex Hilbert spaces with fixed coordinate bases, let $\rho$ be a positive semidefinite trace-one operator on $Q$, and let $|\Psi\rangle\in R\otimes Q$ be a unit vector with $\operatorname{Tr}_R|\Psi\rangle\langle\Psi|=\rho$. The reference $R$ is unchanged. Every channel below is completely positive, trace preserving, and linear on all operators. Entropies $S$ are in bits, with $0\log_2 0=0$. For a channel $\Phi$, write $\sigma_{RQ}=(\operatorname{id}_R\otimes\Phi)(|\Psi\rangle\langle\Psi|)$, $S_e(\rho,\Phi)=S(\sigma_{RQ})$, and $I_e(\rho,\Phi)=S(\Phi(\rho))-S_e(\rho,\Phi)$.
--
--   Assume $I_e(\rho,\Phi)=S(\rho)$. There exists a single CPTP map $\mathcal D:Q\to Q$ restoring the original reference-input pure state and satisfying
--
--   $$
--   \forall v\in\operatorname{supp}\rho,\quad \|v\|=1\ \Longrightarrow\
--   \mathcal D(\Phi(|v\rangle\langle v|))=|v\rangle\langle v|.
--   $$
--
--   Moreover, for every finite coordinate reference $R_{\rm new}=\mathbb C^r$ and every unit vector $|\chi\rangle\in R_{\rm new}\otimes Q$ whose reduced density $\tau_Q=\operatorname{Tr}_{R_{\rm new}}|\chi\rangle\langle\chi|$ has $\operatorname{supp}\tau_Q=\operatorname{supp}\rho$, the same map obeys
--
--   $$
--   (\operatorname{id}_{R_{\rm new}}\otimes(\mathcal D\circ\Phi))(|\chi\rangle\langle\chi|)=|\chi\rangle\langle\chi|.
--   $$
--
--   Recovery is independent of the unknown supported vector and of the new purification's Schmidt coefficients.
-- source:
--   Quantum data processing and error correction, arXiv:quant-ph/9604022v1, PDF p. 17, §6, final support-uniformity paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P06

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.7,14,17: one correction chosen from rho and f restores all unit vectors
in its support and every normalized entangled state with the same Q support.
The new reference is any finite coordinate space, with arbitrary Schmidt weights. -/
theorem recovery_uniform_on_support {R Q : Type*}
    [Fintype R] [Fintype Q] [Nonempty R] [Nonempty Q]
    (rho : Matrix Q Q ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (R × Q)) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = rho)
    (f : Superop Q Q) (hf : IsChannel f)
    (heq : (vnEntropy (f rho) - vnEntropy (idTensorSuperop f (pureDensity psi))) = vnEntropy rho) :
    ∃ d : Superop Q Q, IsChannel d ∧
      idTensorSuperop (R := R) (d ∘ f) (pureDensity psi) = pureDensity psi ∧
      (∀ v : EuclideanSpace ℂ Q, ‖v‖ = 1 → v ∈ LinearMap.range (Matrix.toEuclideanLin rho) →
        d (f (pureDensity v)) = pureDensity v) ∧
      (∀ (r : ℕ) (chi : EuclideanSpace ℂ (Fin r × Q)), ‖chi‖ = 1 →
        LinearMap.range (Matrix.toEuclideanLin (traceLeft (pureDensity chi))) =
          LinearMap.range (Matrix.toEuclideanLin rho) →
        idTensorSuperop (R := Fin r) (d ∘ f) (pureDensity chi) = pureDensity chi) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P06

end
