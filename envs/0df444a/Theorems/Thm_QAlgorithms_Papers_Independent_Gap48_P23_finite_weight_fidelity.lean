-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_finite_weight_fidelity
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.finite_weight_fidelity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:31:56.650998+00:00
-- url     : https://prove2.me/theorems/eece2e40-0a9c-4aad-b7bd-044d2560d745
-- title:
--   Lemma 2.13.
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   For positive odd $n$, symmetric equivariant $f$ and a permutation-invariant, unitary-equivariant channel $\Phi$,
--   $$F_f(\Phi)=\min_{0\le h\le\lfloor n/2\rfloor}\langle f(0^{n-h}1^h)|\Phi(|0^{n-h}1^h\rangle\langle0^{n-h}1^h|)|f(0^{n-h}1^h)\rangle.$$
--   The finite minimum is explicitly attained.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 17, Lemma 2.13.

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

/-- PDF p.17, Lemma 2.13: finite lower-half reduction of the worst case. -/
theorem finite_weight_fidelity (n : ℕ) (hn : 1 ≤ n) (hodd : Odd n)
    (f : Word n 2 → Fin 2) (hf : WordSymmetric f) (he : Equivariant f)
    (Phi : Superop (Word n 2) (Fin 2)) (hPhi : IsChannel Phi)
    (hp : PermutationInvariant Phi) (hu : WordUnitaryEquivariant Phi) :
    IsLeast {r | ∃ h : TwoRowShape n, r = effectProb
      (Matrix.single (f (weightRepresentative n h.val)) (f (weightRepresentative n h.val)) 1)
      (Phi (Matrix.single (weightRepresentative n h.val) (weightRepresentative n h.val) 1))}
      (functionFidelity (fun _ => True) f Phi) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
