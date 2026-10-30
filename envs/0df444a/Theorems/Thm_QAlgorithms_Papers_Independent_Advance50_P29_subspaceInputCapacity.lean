-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_subspaceInputCapacity
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.subspaceInputCapacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:22:19.733988+00:00
-- url     : https://prove2.me/theorems/85c86007-43c7-4d79-ad76-558f5597d040
-- title:
--   §7.5, (26): coherent information of any nonzero subspace input
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. For a nonzero code subspace $C\subset Q$ of dimension $K$, let $\pi_C=\Pi_C/K$. Write $F_e(C,\mathcal N)=\max_{\mathcal R}F_e(\pi_C,\mathcal R\circ\mathcal N)$, where $\mathcal R:B(Q^{\prime})\to B(Q)$ ranges over all CPTP recovery maps and state entanglement fidelity is squared and unconditional. The operational capacity $Q(\mathcal N)$ is the supremum of all real rates $R$ for which one sequence of nonzero codes $C_n\subset Q^{\otimes n}$, one for every positive integer $n$, has $\limsup_n n^{-1}\log_2\dim C_n\ge R$ and $F_e(C_n,\mathcal N^{\otimes n})\to1$. For a state $\rho$, put $I(\rho,\mathcal N)=S(\mathcal N(\rho))-S_e(\rho,\mathcal N)$, where $S$ is von Neumann entropy and $S_e$ is the entropy of the reference/output state after applying $\mathcal N$ to a purification of $\rho$. Let $V\subset Q$ be any nonzero subspace and let $\pi_V=\Pi_V/\dim V$. Then
--
--   $$
--   Q(\mathcal N)\ge I(\pi_V,\mathcal N).
--   $$
--
--   This extends the maximally mixed-input bound to every nonzero subspace, including the whole input space and one-dimensional spaces.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 18, §7.5, (26): coherent information of any nonzero subspace input

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

/-- PDF pp.15,18, (26): every nonzero subspace input gives a capacity lower bound;
there is no assertion that the endpoint rate itself has a code sequence. -/
theorem subspaceInputCapacity [Nonempty I] [Nonempty J]
    (N : Superop I J) (hN : IsChannel N) (C : CodeProjection I) :
    coherentInformation N (codeDensity C) ≤ limsupCodeCapacity N := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
