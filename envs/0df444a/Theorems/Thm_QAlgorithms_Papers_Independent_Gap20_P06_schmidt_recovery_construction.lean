-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P06_schmidt_recovery_construction
-- name    : QAlgorithms.Papers.Independent.Gap20.P06.schmidt_recovery_construction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:18:27.664439+00:00
-- url     : https://prove2.me/theorems/17cd1a4d-330a-4abb-9262-d043fa7a567f
-- title:
--   Positive Schmidt data and the explicit normalized recovery construction
-- statement:
--   Let $Q$ and $R$ be nonzero finite-dimensional complex Hilbert spaces with fixed coordinate bases, let $\rho$ be a positive semidefinite trace-one operator on $Q$, and let $|\Psi\rangle\in R\otimes Q$ be a unit vector with $\operatorname{Tr}_R|\Psi\rangle\langle\Psi|=\rho$. The reference $R$ is unchanged. Every channel below is completely positive, trace preserving, and linear on all operators. Entropies $S$ are in bits, with $0\log_2 0=0$. For a channel $\Phi$, write $\sigma_{RQ}=(\operatorname{id}_R\otimes\Phi)(|\Psi\rangle\langle\Psi|)$, $S_e(\rho,\Phi)=S(\sigma_{RQ})$, and $I_e(\rho,\Phi)=S(\Phi(\rho))-S_e(\rho,\Phi)$.
--
--   Fix any finite nonzero environment $E$, unit vector $|\eta\rangle\in E$, and unitary $U$ on $Q\otimes E$ realizing $\Phi(X)=\operatorname{Tr}_E[U(X\otimes|\eta\rangle\langle\eta|)U^\dagger]$ for every operator $X$. Put $|\Omega\rangle=(I_R\otimes U)(|\Psi\rangle\otimes|\eta\rangle)$, $\sigma_{RE}=\operatorname{Tr}_Q|\Omega\rangle\langle\Omega|$, $\sigma_E=\operatorname{Tr}_Q[U(\rho\otimes|\eta\rangle\langle\eta|)U^\dagger]$, and $\rho_R=\operatorname{Tr}_Q|\Psi\rangle\langle\Psi|$.
--
--   Assume $I_e(\rho,\Phi)=S(\rho)$. There exist positive integers $k,l$, strictly positive weights $(\lambda_i)_{i=1}^k$ and $(\mu_j)_{j=1}^l$, each summing to one, and orthonormal families $(\alpha_i)\subset R$, $(\beta_i)\subset Q$, $(\gamma_j)\subset E$, and $(\phi_{ij})\subset Q$, such that
--
--   $$
--   |\Psi\rangle=\sum_i\sqrt{\lambda_i}\,|\alpha_i\rangle|\beta_i\rangle,\quad
--   \rho=\sum_i\lambda_i|\beta_i\rangle\langle\beta_i|,\quad
--   \sigma_E=\sum_j\mu_j|\gamma_j\rangle\langle\gamma_j|,
--   $$
--   $$
--   |\Omega\rangle=\sum_{i,j}\sqrt{\lambda_i\mu_j}\,|\alpha_i\rangle|\phi_{ij}\rangle|\gamma_j\rangle.
--   $$
--
--   Define $\Pi=I_Q-\sum_{i,j}|\phi_{ij}\rangle\langle\phi_{ij}|$, an additional branch $A_*=\Pi$, and $A_j=\sum_i|\beta_i\rangle\langle\phi_{ij}|$. Then $\Pi^\dagger=\Pi$, $\Pi^2=\Pi$, $\Pi\phi_{ij}=0$, $A_j\phi_{it}=\delta_{jt}\beta_i$, and
--
--   $$
--   \sum_{a\in\{*\}\sqcup\{1,\ldots,l\}} A_a^\dagger A_a=I_Q.
--   $$
--
--   Consequently $\mathcal D(X)=\sum_a A_aXA_a^\dagger$ is a CPTP map satisfying
--
--   $$
--   (\operatorname{id}_R\otimes\mathcal D\otimes\operatorname{id}_E)(|\Omega\rangle\langle\Omega|)
--   =|\Psi\rangle\langle\Psi|\otimes\sigma_E,\qquad
--   (\operatorname{id}_R\otimes(\mathcal D\circ\Phi))(|\Psi\rangle\langle\Psi|)=|\Psi\rangle\langle\Psi|.
--   $$
--
--   This supplies the explicit error-correction process together with its normalization and restoration properties.
-- source:
--   Quantum data processing and error correction, arXiv:quant-ph/9604022v1, PDF p. 15, §6, Schmidt-basis construction, pp.15–17

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P06

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.15--17: under entropy equality, deliver the positive Schmidt data and
the explicit normalized recovery, rather than assuming the factorization.
The last gamma^E on p.16 is gamma^{E1}, as on pp.15 and 17. -/
theorem schmidt_recovery_construction {R Q E : Type*}
    [Fintype R] [Fintype Q] [Fintype E] [Nonempty R] [Nonempty Q] [Nonempty E]
    (rho : Matrix Q Q ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (R × Q)) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = rho)
    (f : Superop Q Q) (hf : IsChannel f)
    (U : Matrix.unitaryGroup (Q × E) ℂ) (eta : EuclideanSpace ℂ E)
    (heta : ‖eta‖ = 1) (hdil : ∀ X, f X = dilationChannel U eta X)
    (heq : (vnEntropy (f rho) - vnEntropy (idTensorSuperop f (pureDensity psi))) = vnEntropy rho) :
    ∃ (k l : ℕ) (lam : Fin k → ℝ) (mu : Fin l → ℝ)
      (alpha : Fin k → EuclideanSpace ℂ R) (beta : Fin k → EuclideanSpace ℂ Q)
      (gamma : Fin l → EuclideanSpace ℂ E)
      (phi : Fin k × Fin l → EuclideanSpace ℂ Q),
      0 < k ∧ 0 < l ∧ (∀ i, 0 < lam i) ∧ (∀ j, 0 < mu j) ∧
      (∑ i, lam i) = 1 ∧ (∑ j, mu j) = 1 ∧
      Orthonormal ℂ alpha ∧ Orthonormal ℂ beta ∧ Orthonormal ℂ gamma ∧
      Orthonormal ℂ phi ∧
      psi = ∑ i, (Real.sqrt (lam i) : ℂ) • tensorVec (alpha i) (beta i) ∧
      rho = ∑ i, (lam i : ℂ) • pureDensity (beta i) ∧
      environmentOutput U eta rho = ∑ j, (mu j : ℂ) • pureDensity (gamma j) ∧
      dilatedVector U eta psi =
        ∑ i, ∑ j, (Real.sqrt (lam i * mu j) : ℂ) •
          tensorVec (alpha i) (tensorVec (phi (i, j)) (gamma j)) ∧
      (let Pi := (1 - ∑ a, pureDensity (phi a))
       let A := recoveryOperators beta phi
       let d := krausApply A
       Piᴴ = Pi ∧ Pi * Pi = Pi ∧
       (∀ i j, act Pi (phi (i, j)) = 0) ∧
       (∀ i j t, act (A (some j)) (phi (i, t)) = if j = t then beta i else 0) ∧
       IsKrausFamily A ∧ IsChannel d ∧
       middleSuperop (R := R) (E := E) d (pureDensity (dilatedVector U eta psi)) =
         appendEnvironment (pureDensity psi) (environmentOutput U eta rho) ∧
       idTensorSuperop (R := R) (d ∘ f) (pureDensity psi) = pureDensity psi) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P06

end
