-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_optimal_template
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.optimal_template
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:42:26.449703+00:00
-- url     : https://prove2.me/theorems/9d573f4d-9785-4bff-8e42-ccc31625b4c2
-- title:
--   Theorem 4.6.
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   For positive odd $n$ and symmetric equivariant Boolean $f$, there is $t\in[0,1]^{\lfloor n/2\rfloor+1}$ such that
--   $$F_f(A_t)=F_f.$$
--   Here $A_t$ is the actually constructed preprocessing followed by the sectorwise mixture of the two physical channels; it is permutation-invariant and unitary-equivariant.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 30, Theorem 4.6.

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

/-- PDF p.30, Theorem 4.6: some interpolation parameters attain the optimum. -/
theorem optimal_template (n : ℕ) (hn : 1 ≤ n) (hodd : Odd n)
    (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (f : Word n 2 → Fin 2) (hf : WordSymmetric f) (he : Equivariant f) :
    ∃ t : TwoRowShape n → ℝ, (∀ k, 0 ≤ t k ∧ t k ≤ 1) ∧
      IsFunctionOptimal (fun _ => True) f (template alpha t) ∧
      PermutationInvariant (template alpha t) ∧ WordUnitaryEquivariant (template alpha t) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
