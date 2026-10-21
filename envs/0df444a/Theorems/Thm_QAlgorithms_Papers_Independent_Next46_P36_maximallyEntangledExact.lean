-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P36_maximallyEntangledExact
-- name    : QAlgorithms.Papers.Independent.Next46.P36.maximallyEntangledExact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:44:37.227996+00:00
-- url     : https://prove2.me/theorems/b36d9af0-a0d9-49cc-b3ea-a713eada4c9e
-- title:
--   Finite-N optimal estimation of supplied two-qubit maximally entangled states
-- statement:
--   Let $N\ge1$ identical copies of a Haar-unknown two-qubit maximally entangled state be supplied. The physical input is $2^{-N/2}\operatorname{vec}(I_{2^N})$ and the action is $U_g^{\otimes N}\otimes I$. Loss is one minus the squared overlap between the single-copy true state and the estimate; arbitrary joint measurements are allowed.
--
--   For $k=0,\ldots,\lfloor N/2\rfloor$, set $t_k=(N\bmod2)+2k=2j_k$ and
--
--   $$c_k=(t_k+1)\sqrt{\frac{\binom N{(N+t_k)/2}}{2^N((N+t_k)/2+1)}}.$$
--
--   Define $C_{kl}=-\frac14(\mathbf1_{k=l,\,t_k>0}+\mathbf1_{k+1=l}+\mathbf1_{l+1=k})$. The optimal risk is attained by a joint POVM, equals the infimum over all admissible joint measurements, and is
--
--   $$R_N=\frac34+\sum_{k,l}c_kC_{kl}c_l.$$
--
--   The spin-zero diagonal is zero: $0\otimes0$ has no spin-one constituent. Consequently, the source's Eq. (65) needs $c_0^2/4$ when $N$ is even. In particular $R_1=1/2$ and $R_2=9/16-\sqrt3/8$. This is measurement optimization for supplied copies, with no optimization of their weights.
-- source:
--   Optimal estimation of group transformations using entanglement, arXiv:quant-ph/0506267v2, PDF p. 9, §IV B, Eq. (61), with correction to (64)-(65)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P36

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P36.matrixMeasurable

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- PDF p.9 Eq.(61): attained finite-N optimal risk. Printed (64)-(65) omit the
spin-zero exception; C_00 is corrected from -1/4 to 0. In particular N=2 gives
9/16-sqrt(3)/8, rather than the uncorrected value. Copies and weights are fixed. -/
theorem maximallyEntangledExact
    [IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ)] [CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ)] [MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ)] [BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (dg : Measure (Matrix.specialUnitaryGroup (Fin 2) ℂ)) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg]
    (N : ℕ) (hN : 1 ≤ N) :
    QAlgorithms.IsState (tensorBell 2 N) ∧ optimalBellRisk dg N = exactBellRisk N ∧
    ∃ M : QAlgorithms.Measurements.DensityPOVM
      (TensorRegister 2 N × TensorRegister 2 N) (Matrix.specialUnitaryGroup (Fin 2) ℂ),
      RepresentationAdmissible (bellAction 2 N) dg bellCost (QAlgorithms.pureDensity (tensorBell 2 N)) M ∧
      representationRisk (bellAction 2 N) dg bellCost (QAlgorithms.pureDensity (tensorBell 2 N)) M = exactBellRisk N ∧
      (∀ L, RepresentationAdmissible (bellAction 2 N) dg bellCost (QAlgorithms.pureDensity (tensorBell 2 N)) L →
        exactBellRisk N ≤ representationRisk (bellAction 2 N) dg bellCost (QAlgorithms.pureDensity (tensorBell 2 N)) L) := by sorry

end QAlgorithms.Papers.Independent.Next46.P36

end
