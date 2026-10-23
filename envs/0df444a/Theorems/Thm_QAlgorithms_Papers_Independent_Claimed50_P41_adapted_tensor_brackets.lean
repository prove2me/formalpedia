-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_adapted_tensor_brackets
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.adapted_tensor_brackets
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:03:52.422386+00:00
-- url     : https://prove2.me/theorems/20ff3e11-7102-4fdd-8af9-f074146e77a1
-- title:
--   §V (5.9)–(5.10): U(n)-adapted tensor brackets
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Let symmetric generators X_ab in a complex algebra satisfy the source Lie-algebra relations (5.4). Split them into V_rs, W_rs and Z_rs as in (5.6). Put J_rs=W_sr-W_rs, Q_rs=V_rs+Z_rs, A_rs=(Q_rs-iJ_rs)/2 and T_lower, T_upper=V-Z respectively minus and plus i(W+W transpose). Write delta for the Kronecker symbol.
--
--   $$
--   [A_{rs},A_{uv}]=\delta_{su}A_{rv}-\delta_{rv}A_{us},\qquad[T_{rs},T^{uv}]=-4(\delta_{ru}A_{sv}+\delta_{rv}A_{su}+\delta_{su}A_{rv}+\delta_{sv}A_{ru}).
--   $$
--
--   The remaining brackets are [A_rs,T_uv]=delta_su T_rv+delta_sv T_ru and [A_rs,T^uv]=-delta_ru T^sv-delta_rv T^su; equal-variance T tensors commute and both tensors are symmetric in their indices. Compact Hermiticity gives A_rs adjoint=A_sr; full generator Hermiticity gives T_lower adjoint=T_upper. This is the U(n)-adapted form of the complete Lie-algebra presentation.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 21, §V (5.9)–(5.10): U(n)-adapted tensor brackets

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.21, (5.9)–(5.10): every adapted tensor bracket in any Lie-algebra
representation. The adjoint conclusions use exactly the compact adaptation,
or full Hermiticity, respectively; no nonunitary representation is called unitary. -/
theorem adapted_tensor_brackets (n : ℕ) (hn : 0 < n)
    (R : Type*) [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
    (rho : GeneratorRepresentation n R) :
    (∀ r s : Fin n, tensorLower rho r s = tensorLower rho s r ∧
      tensorUpper rho r s = tensorUpper rho s r) ∧
    (∀ r s u v : Fin n,
      algebraCommutator (adaptedA rho r s) (adaptedA rho u v) =
        kronecker s u • adaptedA rho r v - kronecker r v • adaptedA rho u s ∧
      algebraCommutator (adaptedA rho r s) (tensorLower rho u v) =
        kronecker s u • tensorLower rho r v + kronecker s v • tensorLower rho r u ∧
      algebraCommutator (adaptedA rho r s) (tensorUpper rho u v) =
        -kronecker r u • tensorUpper rho s v - kronecker r v • tensorUpper rho s u ∧
      algebraCommutator (tensorLower rho r s) (tensorUpper rho u v) =
        (-4 : ℂ) • (kronecker r u • adaptedA rho s v + kronecker r v • adaptedA rho s u +
          kronecker s u • adaptedA rho r v + kronecker s v • adaptedA rho r u) ∧
      algebraCommutator (tensorLower rho r s) (tensorLower rho u v) = 0 ∧
      algebraCommutator (tensorUpper rho r s) (tensorUpper rho u v) = 0) ∧
    ((∀ r s : Fin n, star (compactJ rho r s) = compactJ rho r s ∧
      star (compactQ rho r s) = compactQ rho r s) →
      ∀ r s : Fin n, star (adaptedA rho r s) = adaptedA rho s r) ∧
    ((∀ a b, star (rho.X a b) = rho.X a b) →
      ∀ r s : Fin n, star (tensorLower rho r s) = tensorUpper rho r s) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
