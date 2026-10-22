-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_ideal_choi_matrices
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.ideal_choi_matrices
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:12:32.542944+00:00
-- url     : https://prove2.me/theorems/78347c8d-b3a2-48a1-88ab-fcfa94f09023
-- title:
--   Appendix G.2: explicit exact superoperators
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   Take the six literal output-first Choi matrices of Appendix G.2, with scales $1,1,1/6,1/3,1/3,1/6$ in the order ID, NOT, MAJ3, PAR3, NPAR3, NMAJ3. For their inverse-Choi superoperators,
--   $$\Phi_f(\rho_x^U)=U|f(x)\rangle\langle f(x)|U^\dagger\quad\text{for every }x,U.$$
--   Complete positivity is not assumed. This finite collection does not assert arbitrary-input-size existence or uniqueness.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 84, Appendix G.2: explicit exact superoperators

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

/-- PDF pp.84-85, Appendix G.2: all six literal superoperators implement
exact ideal functionality on every word and common basis. They are not
assumed to be CP; equality with a target density guarantees valid outputs on
the promised products. No arbitrary-n existence or uniqueness is asserted. -/
theorem ideal_choi_matrices :
    (∀ (mask : Fin 2) (x : Word 1 2) (U : Matrix.unitaryGroup (Fin 2) ℂ),
      appendixOneChannel true mask (encodedInput U.val x) = targetDensity U.val (tableFunction 1 mask.val x)) ∧
    (∀ (mask : Fin 4) (x : Word 3 2) (U : Matrix.unitaryGroup (Fin 2) ℂ),
      appendixThreeChannel true mask (encodedInput U.val x) = targetDensity U.val (tableFunction 3 mask.val x)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
