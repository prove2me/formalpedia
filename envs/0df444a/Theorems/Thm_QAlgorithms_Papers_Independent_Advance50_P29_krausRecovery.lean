-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_krausRecovery
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.krausRecovery
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:05:47.425332+00:00
-- url     : https://prove2.me/theorems/7bc03e55-8aaa-4eb1-a776-2f580e1635d6
-- title:
--   §4, (9)–(10): explicit Kraus recovery bound
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. Let $\mathcal N:B(Q)\to B(Q^{\prime})$ be completely positive and trace nonincreasing, with finite Kraus family $(A_i)$ satisfying $\sum_i A_i^\dagger A_i\le I$. The family may be empty and the operation may be zero. For a nonzero code subspace $C\subset Q$ of dimension $K$, let $\pi_C=\Pi_C/K$. Write $F_e(C,\mathcal N)=\max_{\mathcal R}F_e(\pi_C,\mathcal R\circ\mathcal N)$, where $\mathcal R:B(Q^{\prime})\to B(Q)$ ranges over all CPTP recovery maps and state entanglement fidelity is squared and unconditional. For the supplied family $(A_i)_{i\in L}$ define $W_{ij}=A_i^\dagger A_j$ and the operator on $Q\otimes\mathbb C^L$
--   $$
--   D_C=K\sum_{i,j\in L}\left(\pi_CW_{ij}\pi_C-\operatorname{tr}(\pi_CW_{ij}\pi_C)\pi_C\right)\otimes|i\rangle\langle j|.
--   $$
--   Write $\|X\|_{\rm tr}=\operatorname{tr}\sqrt{X^\dagger X}$ and $\|X\|_F^2=\operatorname{tr}(X^\dagger X)$. Set $p=\operatorname{tr}\mathcal N(\pi_C)$. Then
--
--   $$
--   F_e(C,\mathcal N)\ge p-\|D_C\|_{\rm tr}.
--   $$
--
--   This explicit recovery bound includes zero transmission probability and needs no normalization by $p$.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 8, §4, (9)–(10): explicit Kraus recovery bound

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

/-- PDF pp.8–11, (9)–(10): explicit Kraus recovery bound, also when p=0 or the family is empty. -/
theorem krausRecovery [Nonempty I] [Nonempty J] (A : L → Matrix J I ℂ)
    (hA : KrausTraceBound A) (C : CodeProjection I) :
    (krausApply A (codeDensity C)).trace.re - traceNorm (decoupling A C.dimension (codeDensity C)) ≤
      recoveredEntanglementFidelity (krausApply A) (codeDensity C) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
