-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_symmetric_optimal_channel
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.symmetric_optimal_channel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:30:08.756304+00:00
-- url     : https://prove2.me/theorems/f3c4df29-9bc4-4d4b-b5a2-d07d59b2b85e
-- title:
--   Corollary 2.10.
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   For $d\ge2$, $n\ge1$, and every symmetric $f:[d]^n\to[d]$, there is a channel $\Phi$ such that
--   $$F_f(\Phi)=F_f,\qquad \Phi\text{ is permutation-invariant and unitary-equivariant}.$$
--   Both symmetries hold on every input operator.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 16, Corollary 2.10.

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

/-- PDF p.16, Corollary 2.10: an attained optimum with both symmetries. -/
theorem symmetric_optimal_channel (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (f : Word n d → Fin d) (hf : WordSymmetric f) :
    ∃ Phi : Superop (Word n d) (Fin d), IsFunctionOptimal (fun _ => True) f Phi ∧
      PermutationInvariant Phi ∧ WordUnitaryEquivariant Phi := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
