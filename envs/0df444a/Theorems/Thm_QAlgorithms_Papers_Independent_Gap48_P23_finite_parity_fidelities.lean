-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_finite_parity_fidelities
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.finite_parity_fidelities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:13:15.647425+00:00
-- url     : https://prove2.me/theorems/e3359152-63e6-4508-95c4-0ea983c6b643
-- title:
--   §5.1.4: computed parity fidelities
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   At the twenty sizes $n=1,3,\ldots,39$, the exact computed optimal parity fidelities, in order, are
--   $$[1,3/5,5/7,5/9,7/11,7/13,3/5,9/17,11/19,11/21,13/23,13/25,5/9,15/29,17/31,17/33,19/35,19/37,7/13,21/41].$$
--   The subsequent infinite formula (5.4) is conjectural and is not asserted.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 36, §5.1.4: computed parity fidelities

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

/-- PDF p.36, section 5.1.4: finite computed sequence only, not conjecture (5.4). -/
theorem finite_parity_fidelities (i : Fin parityFidelities.length) :
    optimalFunctionFidelity (fun _ => True) (parity (2*i.val+1)) = parityFidelities.get i := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
