-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_conditional_down_chain
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.conditional_down_chain
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:19:11.320031+00:00
-- url     : https://prove2.me/theorems/c674265c-ea28-4c51-bb0b-77d7e1ad8c43
-- title:
--   5.12
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy.
--
--   For either fixed-reference entropy in its DPI range on normalized ABC: Hα↓(AB|C)≥Hα↓(A|BC)+Htilde_∞↓(B|C).
--
--   $$
--   H_\alpha^\downarrow(AB|C)_\rho\ge H_\alpha^\downarrow(A|BC)_\rho+\widetilde H_\infty^\downarrow(B|C)_\rho.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 87, 5.12

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#5.12
5.12, arXiv:1504.00233v5, PDF p.87. -/
theorem conditional_down_chain [Nonempty A] [Nonempty B] [Nonempty C] (r : paperMat ((A × B) × C))
    (hr : IsDensityMatrix r) (sand : Bool) (a : ENNReal) (ha : DPIOrder sand a) :
    conditionalDown sand a (paperRegroup r)+conditionalDown true ⊤ (paperMarginalBC r) ≤ conditionalDown sand a r := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
