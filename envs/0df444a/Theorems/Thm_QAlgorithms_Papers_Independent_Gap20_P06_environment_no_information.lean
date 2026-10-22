-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P06_environment_no_information
-- name    : QAlgorithms.Papers.Independent.Gap20.P06.environment_no_information
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:19:33.395608+00:00
-- url     : https://prove2.me/theorems/5670f47c-06bf-49fd-be12-1a5091682954
-- title:
--   Perfect correction implies no environmental information about any ensemble
-- statement:
--   Let $Q$ and $R$ be nonzero finite-dimensional complex Hilbert spaces with fixed coordinate bases, let $\rho$ be a positive semidefinite trace-one operator on $Q$, and let $|\Psi\rangle\in R\otimes Q$ be a unit vector with $\operatorname{Tr}_R|\Psi\rangle\langle\Psi|=\rho$. The reference $R$ is unchanged. Every channel below is completely positive, trace preserving, and linear on all operators. Entropies $S$ are in bits, with $0\log_2 0=0$. For a channel $\Phi$, write $\sigma_{RQ}=(\operatorname{id}_R\otimes\Phi)(|\Psi\rangle\langle\Psi|)$, $S_e(\rho,\Phi)=S(\sigma_{RQ})$, and $I_e(\rho,\Phi)=S(\Phi(\rho))-S_e(\rho,\Phi)$.
--
--   Fix any finite nonzero environment $E$, unit vector $|\eta\rangle\in E$, and unitary $U$ on $Q\otimes E$ realizing $\Phi(X)=\operatorname{Tr}_E[U(X\otimes|\eta\rangle\langle\eta|)U^\dagger]$ for every operator $X$. Put $|\Omega\rangle=(I_R\otimes U)(|\Psi\rangle\otimes|\eta\rangle)$, $\sigma_{RE}=\operatorname{Tr}_Q|\Omega\rangle\langle\Omega|$, $\sigma_E=\operatorname{Tr}_Q[U(\rho\otimes|\eta\rangle\langle\eta|)U^\dagger]$, and $\rho_R=\operatorname{Tr}_Q|\Psi\rangle\langle\Psi|$.
--
--   Suppose some CPTP recovery $\mathcal D$ gives $F_e(\rho,\mathcal D\circ\Phi)=1$. Then
--
--   $$
--   \sigma_{RE}=\rho_R\otimes\sigma_E.
--   $$
--
--   For every finite pure-state ensemble $\rho=\sum_i p_i|v_i\rangle\langle v_i|$ with $p_i\ge0$, $\sum_i p_i=1$, and $\|v_i\|=1$, the environmental output conditioned on any positive-probability label is the same density:
--
--   $$
--   p_i>0\ \Longrightarrow\
--   \operatorname{Tr}_Q\!\left[U(|v_i\rangle\langle v_i|\otimes|\eta\rangle\langle\eta|)U^\dagger\right]=\sigma_E.
--   $$
--
--   Thus all environmental observables have identical statistics for those ensemble components. This is a necessary consequence of perfect correction; no additional converse is claimed.
-- source:
--   Quantum data processing and error correction, arXiv:quant-ph/9604022v1, PDF p. 18, §7, pp.17–18

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P06

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.17--18: perfect correction implies reference-environment independence
and the same environmental density for every positive-weight component of every
pure-state ensemble of rho. No converse is asserted in this node. -/
theorem environment_no_information {R Q E : Type*}
    [Fintype R] [Fintype Q] [Fintype E] [Nonempty R] [Nonempty Q] [Nonempty E]
    (rho : Matrix Q Q ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (R × Q)) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = rho)
    (f : Superop Q Q) (hf : IsChannel f)
    (U : Matrix.unitaryGroup (Q × E) ℂ) (eta : EuclideanSpace ℂ E)
    (heta : ‖eta‖ = 1) (hdil : ∀ X, f X = dilationChannel U eta X)
    (hcorr : ∃ d : Superop Q Q, IsChannel d ∧ inputEntanglementFidelity psi (d ∘ f) = 1) :
    referenceEnvironment U eta psi =
      Matrix.kronecker (traceRight (pureDensity psi)) (environmentOutput U eta rho) ∧
    (∀ (m : ℕ) (p : Fin m → ℝ) (v : Fin m → EuclideanSpace ℂ Q),
      (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 → (∀ i, ‖v i‖ = 1) →
      (∑ i, (p i : ℂ) • pureDensity (v i)) = rho →
      ∀ i, 0 < p i → environmentOutput U eta (pureDensity (v i)) =
        environmentOutput U eta rho) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P06

end
