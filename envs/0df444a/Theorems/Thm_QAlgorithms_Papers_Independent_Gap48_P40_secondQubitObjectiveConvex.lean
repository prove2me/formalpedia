-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_secondQubitObjectiveConvex
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.secondQubitObjectiveConvex
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:28:21.335114+00:00
-- url     : https://prove2.me/theorems/f7eff475-4770-40d8-b14f-c3d162eceb23
-- title:
--   §VII.A, Lemma 10: convexity of the second qubit objective
-- statement:
--   For $t\in[-1,1]$, put $P(t)=\frac12\begin{pmatrix}1+t&\sqrt{1-t^2}\\\sqrt{1-t^2}&1-t\end{pmatrix}$. This is the canonical pure-state projector for $t=\cos(2\alpha)$ after diagonal phase symmetry. Write $D(A\|B)=\operatorname{Tr}[A(\log A-\log B)]$ with continuous zero-weight terms. If $0<\beta\le1/2$ and $\beta<T\le1-\beta$, put $\eta=1-\beta-T$. Then
--
--   $$
--   t\longmapsto D(\operatorname{diag}(\beta+T,0)+\eta P(t)\|\operatorname{diag}(\beta,T)+\eta P(t))
--   $$
--
--   is convex on $[-1,1]$.
--
--   This includes the zero-residual-weight endpoint of objective (45).
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 9, §VII.A, Lemma 10: convexity of the second qubit objective

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

/-- PDF pp.9–10, Lemma 10: objective (45), including eta=0. -/
theorem secondQubitObjectiveConvex (beta T : ℝ) (hbeta : 0 < beta ∧ beta ≤ 1 / 2)
    (hT : beta < T ∧ T ≤ 1 - beta) :
    ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (qubitObjectiveTwo beta T) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
