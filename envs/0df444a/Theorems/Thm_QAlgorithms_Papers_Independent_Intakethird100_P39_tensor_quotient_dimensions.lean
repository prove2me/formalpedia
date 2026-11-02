-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P39_tensor_quotient_dimensions
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P39.tensor_quotient_dimensions
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:43:53.549864+00:00
-- url     : https://prove2.me/theorems/1df5d4ae-3d71-4730-be73-fb8693e98ab0
-- title:
--   Real dimensions of tensor-factor quotients
-- statement:
--   Let $0\le\mu\le m$ be integers. Write $\mathfrak{su}(d)$ for the real vector space of skew-Hermitian traceless complex $d\times d$ matrices. For $a=2^{m-\mu}$ and $b=2^\mu$, the one-factor subgroup has tangent image $\{A\otimes I_b:A\in\mathfrak{su}(a)\}$; the two-factor subgroup has tangent image consisting of sums $A\otimes I_b+I_a\otimes B$. The real dimensions are
--
--   $$\dim SU(2^m)=4^m-1,$$
--   $$\dim\frac{SU(2^m)}{SU(a)\otimes I_b}=4^{m-\mu}(4^\mu-1),$$
--   $$\dim\frac{SU(2^m)}{SU(a)\otimes SU(b)}=(4^{m-\mu}-1)(4^\mu-1).$$
--
--   These count actual real tangent dimensions. Finite central kernels of the tensor-product subgroup do not alter these dimensions. The formal statement uses the corresponding quotient vector spaces, with subgroup images defined independently of the displayed answers.
-- source:
--   Quantum CISC Compilation by Optimal Control and Scalable Assembly of Complex Instruction Sets beyond Two-Qubit Gates, arXiv:0712.3227v2, PDF p. 4, Real dimensions of block groups and tensor-factor quotients, Eqs. (4)–(6)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P39

namespace QAlgorithms.Papers.Independent.Intakethird100.P39

open scoped BigOperators

/-- PDF p.4, Eqs. (4)-(6): real group and homogeneous-space dimensions,
computed from their tangent spaces rather than defined by the answer. -/
theorem tensor_quotient_dimensions (m mu : ℕ) (hmu : mu ≤ m) :
    Module.finrank ℝ (specialUnitaryTangent (Fin (2 ^ m))) = 4 ^ m - 1 ∧
    Module.finrank ℝ (OneFactorQuotient (2 ^ (m - mu)) (2 ^ mu)) =
      4 ^ (m - mu) * (4 ^ mu - 1) ∧
    Module.finrank ℝ (TwoFactorQuotient (2 ^ (m - mu)) (2 ^ mu)) =
      (4 ^ (m - mu) - 1) * (4 ^ mu - 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P39
