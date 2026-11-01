-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_random_bit_simulation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.random_bit_simulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:58:22.512387+00:00
-- url     : https://prove2.me/theorems/2c59c52d-729d-4116-a2ee-515b8b064b47
-- title:
--   §2.4.5: classical random bit from a Bell pair
-- statement:
--   Apply a Hadamard to the first of two zero bits and a CNOT to copy its classical basis value into the second. The normalized result and its reduced density operator are
--
--   $$
--   |\psi\rangle=\frac{|00\rangle+|11\rangle}{\sqrt2},\qquad
--   \operatorname{Tr}_2(|\psi\rangle\langle\psi|)=\begin{pmatrix}1/2&0\\0&1/2\end{pmatrix}.
--   $$
--
--   Discarding the second bit therefore produces an unbiased classical random bit. This describes local random-bit simulation, without asserting quantum cloning.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 14, §2.4.5: classical random bit from a Bell pair

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.14, §2.4.5: tracing out the copy yields an unbiased classical bit. -/
theorem random_bit_simulation :
    randomBitBell = ((Real.sqrt 2)⁻¹ : ℂ) • (ket (false, false) + ket (true, true)) ∧
    IsState randomBitBell ∧
    traceRight (pureDensity randomBitBell) =
      Matrix.diagonal (fun _ : Bool => (1 / 2 : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
