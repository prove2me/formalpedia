-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_majority_weight_strict_decrease
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.majority_weight_strict_decrease
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:11:09.664745+00:00
-- url     : https://prove2.me/theorems/04f5644b-9b2c-4ee0-bfc5-313ccc517d1b
-- title:
--   Lemma F.2.
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   For odd $n\ge3$, the explicit majority weight fidelity is strictly decreasing on its admissible finite range:
--   $$0\le h<j\le(n-1)/2\quad\Longrightarrow\quad F_n(j)<F_n(h).$$
--   No monotonicity claim beyond that range is made.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 80, Lemma F.2.

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

/-- PDF p.80, Lemma F.2: strictly decreasing only on the admissible finite range. -/
theorem majority_weight_strict_decrease (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    ∀ h j : ℕ, h < j → j ≤ (n-1)/2 → majorityWeightFidelity n j < majorityWeightFidelity n h := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
