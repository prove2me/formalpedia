-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_effect_trace_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P21.effect_trace_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:38:53.231991+00:00
-- url     : https://prove2.me/theorems/34065917-6d43-4d5f-9ad9-1d4702682801
-- title:
--   Corollary 1: effect trace bound from trace norm
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Let $A,B$ be self-adjoint operators, $P$ an effect ($0\le P\le I$), and $\varepsilon>0$. If $\lVert A-B\rVert_1\le\varepsilon$, then
--
--   $$\operatorname{Tr}[P(A-B)]\le\varepsilon.$$
--
--   Here $\lVert\cdot\rVert_1$ is the full trace norm. This controls an effect's expectation by trace-norm distance.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 3, Corollary 1: effect trace bound from trace norm

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P21

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Use the accepted declarations directly; no paper-local aliases hide dimension binders.

open QAlgorithms.Papers.Independent.Claimed50.P33
  (FiniteState IsAverageLocalMonotone IsAdaptiveLOCCMonotone)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

section Statements

variable [Nonempty I] [Nonempty J]

/-- Corollary 1, PDF p.3: full trace norm, self-adjoint operators, and eps>0. -/
theorem effect_trace_bound (A B P : Mat I) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hP : IsEffect P) (eps : ℝ) (heps : 0 < eps) (hd : traceNorm (A - B) ≤ eps) :
    tr (P * (A - B)) ≤ eps := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
