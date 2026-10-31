-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_localZNormalForm
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.localZNormalForm
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:54:44.605007+00:00
-- url     : https://prove2.me/theorems/c6fc4920-b919-4510-8769-c6a83901183a
-- title:
--   Local z-reversal is a normal form
-- statement:
--   Let $n\ge1$ and let $H$ be Hermitian and traceless. Then
--
--   $$H\text{ is type-I locally reversible}\quad\Longleftrightarrow\quad\exists V,\bar H,\boldsymbol\phi:\ H=V\bar H V^\dagger,\qquad K_z(\boldsymbol\phi)\bar H K_z(\boldsymbol\phi)^\dagger=-\bar H,$$
--
--   where $V\in\mathrm{SU}(2)^{\otimes n}$ is local, $\bar H$ is Hermitian and traceless, and $\boldsymbol\phi$ is a vector of independent real z-rotation angles. The normal-form Hamiltonian may be an arbitrary sum. Both directions, including reversibility of every Hamiltonian on such a local orbit, are retained.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 8, Corollary 1: local z reversal is a normal form

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- Corollary 1(1)–(2), PDF p.8: the individual-z normal form is an
arbitrary Hamiltonian, not necessarily one QAlgorithms.kronAll monomial. V is local. -/
theorem localZNormalForm {n : ℕ} (hn : 0 < n) (H : Op (QAlgorithms.Qubits n))
    (hH : IsHamiltonian H) :
    TypeI H ↔ ∃ (V : LocalSU n) (Hbar : Op (QAlgorithms.Qubits n)) (phi : Fin n → ℝ),
      IsHamiltonian Hbar ∧ H = localAd V Hbar ∧
      adjointConjugation (individualZRotation phi) Hbar = -Hbar := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
