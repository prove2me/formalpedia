-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_controlled_qubit
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.controlled_qubit
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:57:24.217888+00:00
-- url     : https://prove2.me/theorems/c5ac96f1-cb92-4cf4-bb2d-d7d28a7a9de5
-- title:
--   §2.4.4 Corollary: controlled one-qubit gate
-- statement:
--   For every one-qubit unitary $U$, controlled $U$ has an exact representation in the basis $Q$, with auxiliary work returned to zero:
--
--   $$
--   |c\rangle|\xi\rangle|0\rangle\longmapsto|c\rangle U^c|\xi\rangle|0\rangle.
--   $$
--
--   The equality holds linearly on the entire two-qubit input space. It retains the relative phase on the control and asserts neither a finite universal gate set nor an optimal gate count.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 14, §2.4.4 Corollary: controlled one-qubit gate

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.14, Corollary: exact clean controlled one-qubit synthesis in Q.
The relative phase on the control is retained, with no approximation parameter. -/
theorem controlled_qubit (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    ∃ (w : ℕ) (c : Circuit kitaevGateBasis (2 + w)),
      ∀ v : EuclideanSpace ℂ (Qubits 2),
        act c.unitary (cleanVector w v) =
          cleanVector w (act (Gate.ofMatrix2 (controlled U)).mat v) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
