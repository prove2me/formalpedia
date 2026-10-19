-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_allOutputSpectralConstraint
-- name    : QAlgorithms.Papers.Independent.Information100.P22.allOutputSpectralConstraint
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:53:47.19079+00:00
-- url     : https://prove2.me/theorems/0d76d324-607d-4ec2-99e5-98f84b41679f
-- title:
--   Corollary 3: Architecture-independent spectral constraint
-- statement:
--   Under the arbitrary-unitary and exact all-output-recovery assumptions above, put $L=2^{(m-1)k}$. There exists a $k$-qubit density operator $\sigma$ and a unitary identification of the signal register with dimensions $2^k\times L$ such that
--   $$\rho_S\simeq\sigma\otimes I_L/L.$$
--   Equivalently, the multiplicity of every eigenvalue of $\rho_S$, including zero if present, is divisible by $L$. No sufficiency for recovery from this spectrum alone is asserted. This refines the entropy obstruction.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 6, Corollary 3: Architecture-independent spectral constraint

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Corollary 3, PDF pp.6,28. Necessary spectral constraint, without claiming recoverability from it. -/
theorem allOutputSpectralConstraint (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (R : EuclideanSpace ℂ (Signals m k × Signals m k)) (hR : IsState R)
    (U : Matrix.unitaryGroup (Qubits k × Signals m k) ℂ)
    (hrec : AllRecoverable R (U : Op _)) :
    SpectralForm (rhoS R) ∧ DivisibleEigenmultiplicities (rhoS R) ∧
    (SpectralForm (rhoS R) ↔ DivisibleEigenmultiplicities (rhoS R)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
