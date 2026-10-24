-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_proposition1
-- name    : QAlgorithms.Papers.Independent.Support50.P17.proposition1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:01:18.621984+00:00
-- url     : https://prove2.me/theorems/76519d27-9453-4d01-b1ea-c78916c1fd89
-- title:
--   Sharp relative-entropy bound for unnormalised equal-trace matrices
-- statement:
--   For $\alpha,T\ge0$, define
--
--   $$
--   q(\alpha,T)=\begin{cases}0,&\alpha=0,\\-\alpha\log(1+T/\alpha),&\alpha>0.\end{cases}
--   $$
--
--   Let $A\ge0$ and $B>0$ be matrices on the same nonzero finite-dimensional complex Hilbert space, with equal trace and $\lambda_{\min}(B)=1$. Put $\alpha=\lambda_{\min}(A)$ and $T=\tfrac12\|A-B\|_1$. Then
--
--   $$
--   T\ge|\alpha-1|,\qquad S(A\|B)\le(1+T)\log(1+T)+q(\alpha,T).
--   $$
--
--   For each fixed $T\ge0$, the function $\alpha\mapsto q(\alpha,T)$ is nonincreasing on $[0,\infty)$. For every $\alpha,T\ge0$ satisfying $T\ge|\alpha-1|$, the explicit matrices
--
--   $$
--   A=\operatorname{Diag}(1+T,\alpha),\qquad B=\operatorname{Diag}(1,T+\alpha)
--   $$
--
--   have the specified traces, minima and trace distance, and attain equality in the bound. Moreover $A>0$ when $\alpha>0$.
--
--   This includes the positive-definite proposition and its explicitly justified semidefinite boundary, without imposing trace one or requiring attainment in each fixed dimension.
-- source:
--   Continuity bounds on the quantum relative entropy - II, arXiv:1105.2656v3, PDF p. 6, Proposition 1: sharp equal-trace unnormalised bound (13)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact frozen support predicate and signed, unnormalised entropy.

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

/-- PDF pp.6–8, Proposition 1, (13): the sharp unnormalised equal-trace bound,
its explicit alpha=0 extension, nonincreasing correction, and the exact 2x2 attaining pair.
The printed “quality” on p.6 means equality, as shown by the p.8 construction. -/
theorem proposition1 :
    (∀ {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
      (A B : Matrix I I ℂ), A.PosSemidef → B.PosDef →
      A.trace = B.trace → minEigenvalue B = 1 →
      let alpha := minEigenvalue A
      let T := traceDistance A B
      |alpha - 1| ≤ T ∧
        relativeEntropy A B ≤
          (((1 + T) * Real.log (1 + T) + zeroExtendedLogCorrection alpha T : ℝ) : EReal)) ∧
    (∀ T : ℝ, 0 ≤ T →
      AntitoneOn (fun alpha => zeroExtendedLogCorrection alpha T) (Set.Ici 0)) ∧
    (∀ alpha T : ℝ, 0 ≤ alpha → 0 ≤ T → |alpha - 1| ≤ T →
      let A := propositionA alpha T
      let B := propositionB alpha T
      A.PosSemidef ∧ B.PosDef ∧ (0 < alpha → A.PosDef) ∧
      A.trace = B.trace ∧ minEigenvalue A = alpha ∧ minEigenvalue B = 1 ∧
      traceDistance A B = T ∧
      relativeEntropy A B =
        (((1 + T) * Real.log (1 + T) + zeroExtendedLogCorrection alpha T : ℝ) : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P17

end
