-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_fDiv_nonnegative
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.fDiv_nonnegative
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:27:35.112834+00:00
-- url     : https://prove2.me/theorems/6680a1ef-7686-44d7-a318-0fa796319d2d
-- title:
--   Proposition 1: Df(P||Q)>=0; if f is strictly convex at 1, equality holds iff P=Q
-- statement:
--   Let $P\ll Q$ be probability measures on any common measurable space. Let $f:(0,\infty)\to\mathbb R$ be convex with $f(1)=0$, using the continuous endpoint and singular-mass conventions of (33)–(37). Then
--
--   $$D_f(P\|Q)\ge0.$$
--
--   If $f$ is strictly convex at 1, equality holds exactly when $P=Q$. Strictness at 1 means every nontrivial chord through 1 lies strictly above $f(1)$; global strict convexity is not required. This is the standard Jensen/Gibbs property recorded in Proposition 1.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 9, Proposition 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Proposition 1: Df(P||Q)>=0; if f is strictly convex at 1, equality holds iff P=Q. Sason--Verdu, arXiv:1508.00335v7, PDF p.9.  -/
theorem fDiv_nonnegative
    (f : ℝ → ℝ) (hf : Generator f) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) :
    0 ≤ fDiv f P Q ∧ (StrictAtOne f → (fDiv f P Q = 0 ↔ P = Q)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
