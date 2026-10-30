-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_randomCodeFidelity
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.randomCodeFidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:06:36.013989+00:00
-- url     : https://prove2.me/theorems/611fc9f7-5504-4cf5-a2b3-19696b75ae9f
-- title:
--   §5, (13) = outline (6): random-code fidelity bound
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. Let $\mathcal N:B(Q)\to B(Q^{\prime})$ be completely positive and trace nonincreasing, with finite Kraus family $(A_i)$ satisfying $\sum_i A_i^\dagger A_i\le I$. The family may be empty and the operation may be zero. For a nonzero code subspace $C\subset Q$ of dimension $K$, let $\pi_C=\Pi_C/K$. Write $F_e(C,\mathcal N)=\max_{\mathcal R}F_e(\pi_C,\mathcal R\circ\mathcal N)$, where $\mathcal R:B(Q^{\prime})\to B(Q)$ ranges over all CPTP recovery maps and state entanglement fidelity is squared and unconditional. Fix any $K$-dimensional seed code $C_0$ and average $C=UC_0$ over normalized Haar measure on the entire unitary group of $Q$; denote this expectation by $[\,\cdot\,]_K$. All displayed Haar integrands are integrable. Let $r=|\mathcal N|$ be the minimum Kraus length and let $\|X\|_F=(\operatorname{tr}X^\dagger X)^{1/2}$. Then
--
--   $$
--   [F_e(C,\mathcal N)]_K\ge\operatorname{tr}\mathcal N(\pi)-\sqrt{Kr}\,\|\mathcal N(\pi)\|_F.
--   $$
--
--   This is the paper's random-code fidelity estimate, valid also for trace-decreasing operations.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 11, §5, (13) = outline (6): random-code fidelity bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P29

open QAlgorithms MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification coherentInformation singleUseInformation mixed)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Dependency50.P48 (wordProbability)

open QAlgorithms.Papers.Independent.Bridge50.P43 (tensorDensity)

open scoped Matrix ComplexConjugate ComplexOrder Topology

attribute [local instance] Classical.propDecidable

variable {I J E L : Type} [Fintype I] [DecidableEq I]

variable [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E]

variable [Fintype L] [DecidableEq L]

/-- PDF pp.7,11–13, (6)=(13): random-code fidelity, with minimal Kraus length and the
unsquared Frobenius norm. Integrability is part of the conclusion. -/
theorem randomCodeFidelity [Nonempty I] [Nonempty J] (N : Superop I J)
    (hN : HasFiniteKrausOperation N) (C : CodeProjection I) :
    Integrable (fun U => recoveredEntanglementFidelity N (rotatedDensity C U))
      (Schur.unitaryHaar (Fintype.card I)) ∧
    (N (mixed I)).trace.re -
      Real.sqrt ((C.dimension : ℝ) * operationLength N) * Real.sqrt (frobeniusSq (N (mixed I))) ≤
        codeAverage C (recoveredEntanglementFidelity N) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
