-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P24_jointTestConcentration
-- name    : QAlgorithms.Papers.Independent.Renew46.P24.jointTestConcentration
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:39:03.560238+00:00
-- url     : https://prove2.me/theorems/8bfdae86-4a6b-4b41-b554-e64d74d1add7
-- title:
--   Proposition 2.1: joint noncommutative test functions concentrate
-- statement:
--   Let $\mathcal H^N$ be nonzero finite-dimensional complex Hilbert spaces and let $X_k^N$ be self-adjoint, uniformly operator-norm bounded in $N$, for each index $k$ in an arbitrary set $K$. Fix radii $r_k>\sup_N\|X_k^N\|$. Suppose nonzero projections $P^N$ concentrate at the real configuration $x=(x_k)$, meaning that every continuous single-variable test has normalized trace limit $F(x_k)$.
--
--   For any complex coefficient function $G$ on finite ordered words $w=(k_1,\ldots,k_m)$ satisfying $\sum_w |G(w)|\prod_i r_{k_i}<\infty$, define $G(X^N)=\sum_w G(w)X_{k_1}^N\cdots X_{k_m}^N$ and $G(x)=\sum_wG(w)\prod_i x_{k_i}$. The empty word contributes the identity. Then
--
--   $$\lim_{N\to\infty}\frac{\operatorname{Tr}(P^NG(X^N))}{\operatorname{Tr}P^N}=G(x).$$
--
--   This extends single-observable concentration to joint ordered analytic tests without assuming commutativity.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, PDF p. 4, Proposition 2.1: joint noncommutative test functions concentrate

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P24

open Filter

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

-- Exact primitives verified against the pinned accepted-library SHA256 catalogue.

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 2.1, PDF pp.4-5, (2.5): all absolutely weighted-summable ordered
noncommutative tests concentrate under a concentrating normalized projection trace. -/
theorem jointTestConcentration {K : Type*} (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (P : OperatorSequence S) (x : K → ℝ)
    (hP : projectionConcentrates S P x) :
    ∀ G : AnalyticTestSeries S,
      Tendsto (fun n => traceExpectation (projectionDensity P n) (operatorEvaluation G n))
        atTop (𝓝 (scalarEvaluation G x)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P24

end
