-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_majority_recursive_fidelity
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.majority_recursive_fidelity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:44:45.276059+00:00
-- url     : https://prove2.me/theorems/97607985-8d57-48ea-9677-212d6a0dd79c
-- title:
--   Lemma 5.1.
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   Let $n\ge1$ be odd. The optimal majority fidelity is
--   $$F_{\rm MAJ}(n)=g((n+1)/2),$$
--   where $g(1)=1$, $g(2)=8/9$, and for $m\ge3$,
--   $$g(m)=\frac{2m}{(2m-1)^2(2m+1)}\left[(2m(4m-7)+5)g(m-1)-4(m-1)(m-2)g(m-2)+1\right].$$
--   The unused total value $g(0)=0$ does not enter the statement.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 36, Lemma 5.1.

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

/-- PDF pp.36,82, Lemma 5.1: exact recursive optimal majority fidelity. -/
theorem majority_recursive_fidelity (n : ℕ) (hn : 1 ≤ n) (hodd : Odd n) :
    optimalFunctionFidelity (fun _ => True) (majority n) = majorityRecurrence ((n+1)/2) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
