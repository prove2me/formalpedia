-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_remark_7_5
-- name    : QAlgorithms.Papers.Independent.Support50.P12.remark_7_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:51:13.942138+00:00
-- url     : https://prove2.me/theorems/cf72ecdc-09dc-489e-8a30-816a1e9c8c04
-- title:
--   Remark 7.5
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized.
--
--   For every fixed prior $0<p<1$ and every noncommutative concrete finite-dimensional observable algebra,
--
--   $$D_p(\rho\Vert\sigma)=1-\|p\rho-(1-p)\sigma\|_1$$
--
--   cannot be represented as $S_f$ on all density pairs by any admissible generator. The quantifier over each fixed prior is retained.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 36, Remark 7.5

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- Remark 7.5, PDF p.36: every fixed nondegenerate prior has its own impossibility. -/
theorem remark_7_5 [Nonempty I] (A : Alg I) (ha : Noncommutative A) (p : ℝ) (hp : p ∈ Ioo 0 1) :
    ¬ ∃ f, RepresentsStateDivergence A (fun rho sigma =>
      ((1 - QAlgorithms.traceNorm ((p : ℂ) • rho - ((1 - p : ℝ) : ℂ) • sigma) : ℝ) : EReal)) f := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
