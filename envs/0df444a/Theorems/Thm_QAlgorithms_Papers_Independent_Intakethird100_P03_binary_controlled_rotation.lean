-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_binary_controlled_rotation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.binary_controlled_rotation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:57:53.187072+00:00
-- url     : https://prove2.me/theorems/3c7ec6ee-9814-4edb-b093-aa3ed4260ebf
-- title:
--   §2.4.4: state preparation with binary angle control
-- statement:
--   Let $x_1,\ldots,x_b$ be a finite binary angle code, and put
--
--   $$
--   \theta(x)=2\pi\sum_{s=1}^b x_s2^{-s}.
--   $$
--
--   There is an exact $Q$ operation sequence, with clean work, which performs
--
--   $$
--   |x\rangle|0\rangle\longmapsto|x\rangle\bigl(\cos\theta(x)|0\rangle+\sin\theta(x)|1\rangle\bigr).
--   $$
--
--   Correctness on these basis codes extends linearly to coherent control superpositions. For $b=0$, the angle is zero.
--
--   This is the finite real-coefficient state preparation claimed in the paragraph, without claiming finite exact codes for arbitrary real numbers.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 14, §2.4.4: state preparation with binary angle control

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.14: finite binary-angle controlled state preparation, exactly and with
clean work. Correctness on these basis inputs extends linearly to coherent controls. -/
theorem binary_controlled_rotation (b : ℕ) :
    ∃ (w : ℕ) (c : Circuit kitaevGateBasis ((b + 1) + w)), ∀ x : Qubits b,
      act c.unitary (inputState (Fin.snoc x false) w) = cleanVector w (rotatedZero x) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
