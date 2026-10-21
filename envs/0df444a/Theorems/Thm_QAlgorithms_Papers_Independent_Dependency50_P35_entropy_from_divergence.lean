-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_entropy_from_divergence
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.entropy_from_divergence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:58:01.706024+00:00
-- url     : https://prove2.me/theorems/9d021583-db43-44d3-88b9-2aa361078660
-- title:
--   Equation (5): unconditional entropy from divergence
-- statement:
--   Let $\rho\ge0$ satisfy $0<\operatorname{Tr}\rho\le1$, and let $\alpha>0$. Let $P_\rho$ be the support projector, $d=\operatorname{rank}\rho>0$, and $\pi=P_\rho/d$. With $H_\alpha(\rho)=(1-\alpha)^{-1}\log_2(\operatorname{Tr}\rho^\alpha/\operatorname{Tr}\rho)$ and the Petz divergence $D_\alpha$, both continuously extended at one,
--
--   $$
--   H_\alpha(\rho)=-D_\alpha(\rho\|P_\rho)=\log_2d-D_\alpha(\rho\|\pi)=H_\alpha(\pi)-D_\alpha(\rho\|\pi).
--   $$
--
--   The references commute with $\rho$, so the same divergences are sandwiched divergences. The formula expresses entropy as a deficit from the maximal entropy on the actual support.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 10, Equation (5)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.10, (5): support identity and support rank; includes order one via
continuous extensions of the unconditional entropy and Petz divergence. -/
theorem entropy_from_divergence {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (ha : 0 < a) (rho : Mat I) (hr : Substate rho) :
    (renyiEntropy a rho : EReal) = -petz a rho (supportId rho) ∧
    (renyiEntropy a rho : EReal) = (Real.logb 2 (supportRank rho : ℝ) : EReal) -
      petz a rho (supportMixed rho) ∧
    (renyiEntropy a rho : EReal) = (renyiEntropy a (supportMixed rho) : EReal) -
      petz a rho (supportMixed rho) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
