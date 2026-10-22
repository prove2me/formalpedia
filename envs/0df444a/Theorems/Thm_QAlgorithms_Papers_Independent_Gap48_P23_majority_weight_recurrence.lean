-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_majority_weight_recurrence
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.majority_weight_recurrence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:10:14.268006+00:00
-- url     : https://prove2.me/theorems/9aaac3cf-a610-4f58-9275-344b08d5cf38
-- title:
--   Lemma F.1.
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   Let $n\ge1$ be odd and let $F_n(h)$ be the explicit sum (5.6). Then $F_n(0)=1$, and for $1\le h\le(n-1)/2$,
--   $$F_n(h)=a(n,h)F_n(h-1)+b(n,h),$$
--   where $a=(n-2h)h/[(n-2h+2)(n-h+1)]$ and $b=[4h^2-(4n+5)h+(n+1)(n+2)]/[(n-2h+2)(n-h+1)]$. The recurrence is not applied at zero.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 80, Lemma F.1.

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

/-- PDF p.80, Lemma F.1: base and recurrence on its stated finite domain. -/
theorem majority_weight_recurrence (n : ℕ) (hn : 1 ≤ n) (hodd : Odd n) :
    majorityWeightFidelity n 0 = 1 ∧
    ∀ h : ℕ, 1 ≤ h → h ≤ (n-1)/2 →
      majorityWeightFidelity n h = recurrenceA n h * majorityWeightFidelity n (h-1) + recurrenceB n h := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
