-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P06_pairReading_tensorDescription
-- name    : QAlgorithms.Papers.Independent.Independent1.P06.pairReading_tensorDescription
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:44:04.90698+00:00
-- url     : https://prove2.me/theorems/9572bec4-4611-485c-ac11-7ff82c16f7e1
-- title:
--   Lemma 3.3: pair reading tensor description
-- statement:
--   Let $H_X\in\mathbb F_2^{m_X\times n}$ and $H_Z\in\mathbb F_2^{m_Z\times n}$ satisfy $H_XH_Z^T=0$, and let $P=(1\;1)$. In the product bases, the three coboundaries of the pair-reading deformation are
--
--   $$D_X^T=\begin{bmatrix}I_2\otimes H_X^T\\P\otimes I_{m_X}\end{bmatrix},\quad D_Z^T=\begin{bmatrix}I_2\otimes H_Z^T&P^T\otimes I_n\\0&I_1\otimes H_X\end{bmatrix},\quad D_M^T=\begin{bmatrix}P^T\otimes I_{m_Z}\\I_1\otimes H_Z^T\end{bmatrix}.$$
--
--   Here old data precede new data, and old Z checks precede new Z checks; $D_M$ denotes the metachecks. These are the explicit tensor-product differentials, retaining the final degree as in pp.21-22.
-- source:
--   Fast and fault-tolerant logical measurements: Auxiliary hypergraphs and transversal surgery, arXiv:2510.14895v1, Lemma 3.3, PDF p. 18. https://arxiv.org/abs/2510.14895v1 . PDF SHA-256: 5432b21da79d052ade1546bd9aa83b711bc517ad598c27fc785a711aeaafe54e.

import Definitions.Def_QAlgorithms_Defs_SurgeryFaultComplexes
import Definitions.Def_QAlgorithms_Defs_MitigationOperationBasis
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P06_Model
set_option autoImplicit false

/-!
# Fast and fault-tolerant logical measurements (arXiv:2510.14895v1)

Paper-local definitions and statement-only targets. Deferred nodes are recorded in the
assigned unit's HARD.md and GAPS.json. No operational fault-distance lower bound is
inferred from the open-boundary homology calculation.
-/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P06









/-- Lemma 3.3, PDF pp.18–19, with the metacheck term retained as on pp.21–22:
all three coboundaries of Eq.(2), in the displayed tensor-product bases, are precisely
those of C tensor (F2^2 --[1 1]--> F2). The matrix types specify all four degrees. -/
theorem pairReading_tensorDescription {n mx mz : ℕ}
    (HX : Matrix (Fin mx) (Fin n) F2) (HZ : Matrix (Fin mz) (Fin n) F2)
    (css : HX * HZ.transpose = 0) :
    (readingX HX pairPattern).transpose =
      Matrix.fromRows
        (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) F2) HX.transpose)
        (Matrix.kronecker pairPattern (1 : Matrix (Fin mx) (Fin mx) F2)) ∧
    (readingZ HX HZ pairPattern).transpose =
      Matrix.fromBlocks
        (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) F2) HZ.transpose)
        (Matrix.kronecker pairPattern.transpose (1 : Matrix (Fin n) (Fin n) F2))
        0 (Matrix.kronecker (1 : Matrix (Fin 1) (Fin 1) F2) HX) ∧
    (readingMeta HZ pairPattern).transpose =
      Matrix.fromRows
        (Matrix.kronecker pairPattern.transpose (1 : Matrix (Fin mz) (Fin mz) F2))
        (Matrix.kronecker (1 : Matrix (Fin 1) (Fin 1) F2) HZ.transpose) := by sorry






































end QAlgorithms.Papers.Independent.Independent1.P06
