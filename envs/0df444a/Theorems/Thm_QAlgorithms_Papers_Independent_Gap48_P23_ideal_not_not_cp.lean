-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_ideal_not_not_cp
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.ideal_not_not_cp
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:28:19.183983+00:00
-- url     : https://prove2.me/theorems/389146ab-4114-41d5-a0d6-ee03921a4c7c
-- title:
--   §2.4: ideal universal NOT is not CP
-- statement:
--   All spaces are finite-dimensional over the complex numbers, with their indicated computational bases. Choi matrices are unnormalized and ordered output tensor input.
--
--   The complex-linear ideal NOT is $\mathcal N(X)=\operatorname{Tr}(X)I-X$. Its Choi matrix in output-first order is
--   $$J(\mathcal N)=\begin{pmatrix}0&0&0&-1\\0&1&0&0\\0&0&1&0\\-1&0&0&0\end{pmatrix}.$$
--   It is not completely positive and is not a channel. Complete positivity is tested against every finite reference system.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 14, §2.4: ideal universal NOT is not CP

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF p.14, (2.25): exact Choi matrix and CP obstruction for the ideal NOT. -/
theorem ideal_not_not_cp :
    (∀ a b : Fin 2 × Fin 2, functionOutputChoi idealNot a b =
      (!![0,0,0,-1; 0,1,0,0; 0,0,1,0; -1,0,0,0] : Op (Fin 4))
        ⟨2*a.1.val+a.2.val, by omega⟩ ⟨2*b.1.val+b.2.val, by omega⟩) ∧
    ¬ CompletelyPositive idealNot ∧ ¬ IsChannel idealNot := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
