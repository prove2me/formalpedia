-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_firstQubitObjectiveConvex
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.firstQubitObjectiveConvex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:27:48.907906+00:00
-- url     : https://prove2.me/theorems/40db986b-a43a-45a0-b8a6-bb50e65aea89
-- title:
--   §VII.A, Lemma 9: convexity of the first qubit objective
-- statement:
--   For $t\in[-1,1]$, put $P(t)=\frac12\begin{pmatrix}1+t&\sqrt{1-t^2}\\\sqrt{1-t^2}&1-t\end{pmatrix}$. This is the canonical pure-state projector for $t=\cos(2\alpha)$ after diagonal phase symmetry. Write $D(A\|B)=\operatorname{Tr}[A(\log A-\log B)]$ with continuous zero-weight terms. If $0<\beta\le1/2$ and $0\le T\le\beta$, then
--
--   $$
--   t\longmapsto D(\operatorname{diag}(\beta+T,\beta-T)+(1-2\beta)P(t)\|\beta I+(1-2\beta)P(t))
--   $$
--
--   is convex on $[-1,1]$.
--
--   This states convexity of the source objective (44) itself.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 9, §VII.A, Lemma 9: convexity of the first qubit objective

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

/-- PDF p.9, Lemma 9: convexity of the actual objective (44). -/
theorem firstQubitObjectiveConvex (beta T : ℝ) (hbeta : 0 < beta ∧ beta ≤ 1 / 2)
    (hT : 0 ≤ T ∧ T ≤ beta) :
    ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (qubitObjectiveOne beta T) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
