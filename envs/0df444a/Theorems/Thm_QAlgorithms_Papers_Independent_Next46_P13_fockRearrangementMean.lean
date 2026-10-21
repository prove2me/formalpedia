-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P13_fockRearrangementMean
-- name    : QAlgorithms.Papers.Independent.Next46.P13.fockRearrangementMean
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:09:55.004359+00:00
-- url     : https://prove2.me/theorems/7c400ec8-5e82-4631-a955-d4b8a945ea4f
-- title:
--   Lemma 7: Fock rearrangement lowers photon mean
-- statement:
--   Let $\rho$ be any one-mode positive trace-class state of trace one, without a full-rank or finite-energy restriction. If $x_0\ge x_1\ge\cdots$ are its eigenvalues counted with multiplicity, define its Fock rearrangement by $\rho^\downarrow=\sum_{k\ge0}x_k|k\rangle\langle k|$. With $\hat n=a^\dagger a$,
--
--   $$\operatorname{tr}(\hat n\rho^\downarrow)\le\operatorname{tr}(\hat n\rho).$$
--
--   Both expectations take values in $[0,+\infty]$. The result orders the physical photon mean under passive rearrangement, including states of infinite mean.
--
--   **Formalization Note** Ordered eigenvalues are computed as approximation numbers, and the conclusion certifies the resulting matrix is a normalized density.
-- source:
--   Geometric inequalities from phase space translations, arXiv:1606.08603v2, PDF p. 21, Lemma 7

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P13

/-- PDF p.21, Lemma 7: no finite-energy or full-rank restriction in Section 5. -/
theorem fockRearrangementMean (X : B.FockOperator) (hX : B.IsDensity X) :
    B.HasFockMatrix (passive X) (fun m n => if m = n then (C.eigenvalue X n : ℂ) else 0) ∧
      B.IsDensity (passive X) ∧ photonMeanExtended (passive X) ≤ photonMeanExtended X := by sorry

end QAlgorithms.Papers.Independent.Next46.P13

end
