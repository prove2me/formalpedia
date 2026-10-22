-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_optimal_choi_matrices
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.optimal_choi_matrices
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:11:50.131954+00:00
-- url     : https://prove2.me/theorems/827209a2-bbae-4748-9b47-0fde19021cd6
-- title:
--   Appendix G.1: explicit optimal Choi matrices
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   Take the six literal output-first Choi matrices of Appendix G.1, with scales $1,1/3,1/9,1/15,1/5,1/45$ for ID, NOT, MAJ3, PAR3, NPAR3, NMAJ3. Their inverse-Choi maps are channels attaining
--   $$F_f(\Phi_f)=F_f.$$
--   The word coordinates are lexicographic with the first bit most significant. Every printed entry is fixed by the explicit row layout and numerical constants.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 82, Appendix G.1: explicit optimal Choi matrices

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

/-- PDF pp.82-84, Appendix G.1: all six literal maps are optimal quantum
channels. Their precise input/output basis order is fixed above. -/
theorem optimal_choi_matrices :
    (∀ mask : Fin 2, IsFunctionOptimal (fun _ => True) (tableFunction 1 mask.val) (appendixOneChannel false mask)) ∧
    (∀ mask : Fin 4, IsFunctionOptimal (fun _ => True) (tableFunction 3 mask.val) (appendixThreeChannel false mask)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
