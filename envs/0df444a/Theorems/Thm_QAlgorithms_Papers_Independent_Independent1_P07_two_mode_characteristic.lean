-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P07_two_mode_characteristic
-- name    : QAlgorithms.Papers.Independent.Independent1.P07.two_mode_characteristic
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:48:39.704288+00:00
-- url     : https://prove2.me/theorems/fca8fe83-a599-4f21-8fa3-4471d789f7af
-- title:
--   Two-mode covariance characteristic polynomial
-- statement:
--   Let $\gamma=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$ be a positive definite physical two-mode covariance matrix, so $A,B$ are real symmetric $2\times2$ matrices and $\gamma+i\sigma/2\ge0$. Use $\sigma=\operatorname{diag}(J,J)$ with $J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$, and let $\gamma^{T_A}$ reverse Alice's momentum. Then
--
--   $$\det(\xi I-\sigma^{-1}\gamma^{T_A})=\xi^4+(\det A+\det B-2\det C)\xi^2+\det\gamma.$$
--
--   The polynomial's plus sign is retained; its roots occur as imaginary symplectic pairs.
--
--   **Correction to the printed source.**
--
--   Printed: PDF p.9 prints the standard block [[0,1],[1,0]] and describes the roots near Eq.(64) as real pairs.
--
--   Corrected: Use J=[[0,1],[-1,0]], explicitly in symplecticTwo and the covariance hypothesis; preserve every coefficient of Eq.(64).
--
--   Reason: Eq.(54) explicitly requires an antisymmetric symplectic form; the preceding normal-mode paragraph gives imaginary eigenvalue pairs. At the physical vacuum gamma=I/2 the characteristic polynomial is (X^2+1/4)^2. The symmetric printed block would give (X^2-1/4)^2. This is the minimal sign repair consistent with the source's commutation convention.
-- source:
--   A computable measure of entanglement, arXiv:quant-ph/0102117v1, §V.C, Eq. (64), PDF p. 9. https://arxiv.org/abs/quant-ph/0102117v1 . PDF SHA-256: a6bc5031b04d93cf18e71e39425eea8b9b8c938252bb87d8067d890269b90f7b.

import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P07_Model
set_option autoImplicit false

/-! Vidal–Werner, arXiv:quant-ph/0102117v1. All locators are PDF pages.
Paper-local operational and variational definitions precede their statements.
Deferred source inconsistencies and interfaces are recorded in HARD.md. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P07

open Entanglement


















































/-- Eq. (64), PDF p. 9, retaining its plus sign. Printed: the standard block
has lower-left +1, and the nearby roots are written as real pairs. Changed: use
lower-left -1 in symplecticTwo. Why: Eq. (54) requires antisymmetry and the
earlier normal-mode paragraph gives imaginary root pairs. No coefficient of
the displayed characteristic polynomial is changed. -/
theorem two_mode_characteristic (A B C : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.IsSymm) (hB : B.IsSymm)
    (hpositive : (Matrix.fromBlocks A C C.transpose B).PosDef)
    (hphysical : ((Matrix.fromBlocks A C C.transpose B).map (algebraMap ℝ ℂ) +
      (Complex.I/2) • symplecticTwo.map (algebraMap ℝ ℂ)).PosSemidef) :
    let gamma := Matrix.fromBlocks A C C.transpose B
    let gammaTA := momentumReversal*gamma*momentumReversal
    (symplecticTwo⁻¹*gammaTA).charpoly =
      Polynomial.X^4+Polynomial.C (A.det+B.det-2*C.det)*Polynomial.X^2+
        Polynomial.C gamma.det := by sorry














end QAlgorithms.Papers.Independent.Independent1.P07
