-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P01_qubitCG_three_logical_operations
-- name    : QAlgorithms.Papers.Independent.Gap20.P01.qubitCG_three_logical_operations
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:11:38.770982+00:00
-- url     : https://prove2.me/theorems/ca91ba80-1636-4766-80a8-8a929f283e8c
-- title:
--   The qubit CG step is three logical register operations
-- statement:
--   Let $j=2J$ be a nonnegative integer and let $m=2m_{\rm phys}$ be an integer with $-j\le m\le j$ and $m+j$ even. Encode the added spin by a bit $b$, with $s_b=-1$ for false and $s_b=1$ for true, and put $M=m+s_b$. These are doubled spin and magnetic coordinates. Let $C(j,j';m,M,b)$ be the real, normalized add-spin-$1/2$ Clebsch–Gordan coefficient in the accepted convention, with zero coefficients for inadmissible labels.
--
--   Apply the following three linear register operations: add $s_b$ to the magnetic register, apply the controlled rotation $\begin{pmatrix}c&-s\\s&c\end{pmatrix}$ to the bit, and add the new bit's sign to the spin register. Here $c=\sqrt{(j+M+1)/(2(j+1))}$ and $s=\sqrt{(j-M+1)/(2(j+1))}$. The result is exactly
--
--   $$
--   |j,m,b\rangle\longmapsto C(j,j-1;m,M,b)|j-1,M,\mathrm{false}\rangle+C(j,j+1;m,M,b)|j+1,M,\mathrm{true}\rangle.
--   $$
--
--   The bit records the lower or upper coupling path. At $j=0$ the lower coefficient is zero. The identity extends linearly to superpositions of valid inputs and specifies an exact logical CG step. These three operations act on entire registers; their elementary gate synthesis is a separate question.
-- source:
--   Efficient Quantum Circuits for Schur and Clebsch-Gordan Transforms, arXiv:quant-ph/0407082v4, PDF p. 2, Eq.(6), Fig.1; continued on PDF p.3

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P01

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Gap20.P01

open QAlgorithms.Papers.Independent.Support21.P09 (Rep UnitaryRep elementaryGates)

/-- PDF pp.2--3, Eq.(6) and Fig.1: the exact qubit Clebsch--Gordan
analysis is the three named logical register operations, in that order.
Magnetic admissibility includes the half-integer parity restriction.
Linearity supplies the same identity on every superposition of valid inputs.
This makes no assertion that the three operations are elementary gates. -/
theorem qubitCG_three_logical_operations (j : ℕ) (m : ℤ) (b : Bool)
    (hm : QAlgorithms.Papers.Independent.Renew46.P01.MagneticAdmissible j m) :
    addSpin (rotateBranch (addMagnetic (Finsupp.single ((j : ℤ), m, b) 1))) =
      qubitCGTarget j m b := by sorry

end QAlgorithms.Papers.Independent.Gap20.P01

end
