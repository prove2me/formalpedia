-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_reducible_residues
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.reducible_residues
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:27:24.456255+00:00
-- url     : https://prove2.me/theorems/bbcc7390-6967-4a01-a0e3-dbbac398b098
-- title:
--   Remark 7.5: reducible residues
-- statement:
--   Let $R=\mathbb Z[\omega]/(2)$, whose elements are written $pqrs=p\omega^3+q\omega^2+r\omega+s$ with binary coefficients. A residue $x$ is reducible when $x=\rho(\sqrt2)y$ for some $y\in R$. Then
--
--   $$
--   x\text{ is reducible}\quad\Longleftrightarrow\quad x\in\{0000,0101,1010,1111\}.
--   $$
--   Multiplication is the quotient-ring multiplication with $\omega^4+1=0$ over $\mathbb F_2$. This is the complete reducibility classification.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 8, Remark 7.5: reducible residues

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Remark 7.5, PDF p.8: complete classification in Z[omega]/(2), using the
source's pqrs convention rather than reduction modulo sqrt(2). -/
theorem reducible_residues (r : Residue) :
    Reducible r ↔ r = bits 0 ∨ r = bits 5 ∨ r = bits 10 ∨ r = bits 15 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
