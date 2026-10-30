-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_theorem2
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.theorem2
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:11:55.226952+00:00
-- url     : https://prove2.me/theorems/4d2a1359-7c4a-4a07-a9a1-9ae455c2679b
-- title:
--   Theorem 2: two-copy invariant purity classifier
-- statement:
--   An $n$-qubit input $\rho$ is a positive semidefinite, trace-one matrix on the fixed computational basis, of dimension $d=2^n$. A $k$-copy model has a fixed input-independent unitary $U$, a Hermitian observable $O$, effective observable $\widetilde O=U^\dagger O U$, and exact response $h(\rho)=\operatorname{Tr}[U\rho^{\otimes k}U^\dagger O]$. Fix $n\ge1$, $d=2^n$, and $1/d\le b<1$, with nonempty classes of purity $1$ and $b$. Write $R_b$ for their union and $p(\rho)=\operatorname{Tr}(\rho^2)$. For every pair of fixed real numbers $a,s$, there exists a two-copy model satisfying
--
--   $$\widetilde O=aI+s\,\mathrm{SWAP},\qquad h(\rho)=a+s\operatorname{Tr}(\rho^2).$$
--
--   It is $U(d)$-invariant on all density matrices. If $s\ne0$, its exact output sets for the two purity classes are disjoint. The choice $(a,s)=(0,1)$ returns purity exactly. There is no gate-count or finite-shot claim.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 7, Theorem 2: two-copy invariant purity classifier

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

/-- PDF pp.7–8, Theorem 2 and Eq.(15): all real affine combinations are
realizable, invariant, and separating when the swap coefficient is nonzero.
The coefficient choice (0,1) gives purity exactly. -/
theorem theorem2 {n : ℕ} (hn : 1 ≤ n) (b : ℝ)
    (hb : 1 / (2 : ℝ) ^ n ≤ b ∧ b < 1)
    (hpure : ∃ rho : Mat (Qubits n), IsDensityMatrix rho ∧ purity rho = 1)
    (hmixed : ∃ rho : Mat (Qubits n), IsDensityMatrix rho ∧ purity rho = b) :
    ∀ a s : ℝ, ∃ M : ExpectationModel (Qubits n) 2,
      M.effective = (a : ℂ) • 1 + (s : ℂ) • copySwap (Qubits n) ∧
      DomainInvariant (Matrix.unitaryGroup (Qubits n) ℂ : Set (Mat (Qubits n)))
        {rho | IsDensityMatrix rho} M.response ∧
      (∀ rho, IsDensityMatrix rho → M.response rho = a + s * purity rho) ∧
      (s ≠ 0 → SeparatesPurity b M.response) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
