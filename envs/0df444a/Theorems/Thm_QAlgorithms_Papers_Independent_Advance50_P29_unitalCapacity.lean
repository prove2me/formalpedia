-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_unitalCapacity
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.unitalCapacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:09:20.567048+00:00
-- url     : https://prove2.me/theorems/42daaf37-fb78-4416-9532-3acfc211de76
-- title:
--   §6, (24): random coding attains the unital-channel Hamming rate
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. For a nonzero code subspace $C\subset Q$ of dimension $K$, let $\pi_C=\Pi_C/K$. Write $F_e(C,\mathcal N)=\max_{\mathcal R}F_e(\pi_C,\mathcal R\circ\mathcal N)$, where $\mathcal R:B(Q^{\prime})\to B(Q)$ ranges over all CPTP recovery maps and state entanglement fidelity is squared and unconditional. The operational capacity $Q(\mathcal N)$ is the supremum of all real rates $R$ for which one sequence of nonzero codes $C_n\subset Q^{\otimes n}$, one for every positive integer $n$, has $\limsup_n n^{-1}\log_2\dim C_n\ge R$ and $F_e(C_n,\mathcal N^{\otimes n})\to1$. Let $\mathcal U$ be a normalized-unital CPTP channel and $r=|\mathcal U|$ its minimum Kraus length. Then
--
--   $$
--   Q(\mathcal U)\ge\log_2D-\log_2r.
--   $$
--
--   This is the explicit quantum Hamming-rate lower bound obtained by random coding. It remains meaningful if the right side is nonpositive.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 14, §6, (24): random coding attains the unital-channel Hamming rate

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

/-- PDF p.14, (24): random coding attains the normalized-unital Hamming rate. -/
theorem unitalCapacity [Nonempty I] [Nonempty J] (N : Superop I J)
    (hN : IsChannel N) (hu : NormalizedUnital N) :
    Real.logb 2 (Fintype.card J : ℝ) - Real.logb 2 (operationLength N : ℝ) ≤
      limsupCodeCapacity N := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
