-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_site_impurity
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.site_impurity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:16:00.415541+00:00
-- url     : https://prove2.me/theorems/347b8fbc-d52d-4e18-8775-fb8cda254363
-- title:
--   Eq.(34): single-site impurity response
-- statement:
--   An $n$-qubit input $\rho$ is a positive semidefinite, trace-one matrix on the fixed computational basis, of dimension $d=2^n$. A $k$-copy model has a fixed input-independent unitary $U$, a Hermitian observable $O$, effective observable $\widetilde O=U^\dagger O U$, and exact response $h(\rho)=\operatorname{Tr}[U\rho^{\otimes k}U^\dagger O]$. Let $\rho=|\psi\rangle\langle\psi|$ be a pure $n$-qubit density matrix with $\|\psi\|=1$, and let $\rho_Q=\operatorname{Tr}_{S\setminus Q}\rho$ for $S=\{1,\ldots,n\}$. For two copies, $S_Q$ swaps the copies at precisely the sites in $Q$ and acts as identity elsewhere. Assume $n\ge1$ and choose site $j\in S$. A two-copy model with $\widetilde O=2(I-S_{\{j\}})$ satisfies
--
--   $$h(\rho)=2\bigl(1-\operatorname{Tr}(\rho_{\{j\}}^2)\bigr).$$
--
--   This is the displayed single-site impurity response across the site-versus-rest cut, with identity on all other paired sites.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 13, Eq.(34): single-site impurity response

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.13, Eq.(34): the response is twice the one-site linear entropy. -/
theorem site_impurity {n : ℕ} (hn : 1 ≤ n) (j : Fin n)
    (M : ExpectationModel (Qubits n) 2)
    (hobs : M.effective = (2 : ℂ) • (1 - subsystemSwap {j}))
    (rho : Mat (Qubits n)) (hpure : IsPure rho) :
    M.response rho = 2 * (1 - purity (subsystemReduction (fun _ => Bool) rho {j})) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
