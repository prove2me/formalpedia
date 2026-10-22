-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_petz_threeConditions
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.petz_threeConditions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:46:10.220155+00:00
-- url     : https://prove2.me/theorems/0d372677-1cad-434e-b53a-7d8f4bfc60cf
-- title:
--   Theorem 1: Petz equivalence, including the degenerate-state extension proved in Appendix 5.1
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Let $\rho,\sigma$ be states with $D(\rho\|\sigma)<\infty$, and let $\Theta_\sigma$ be the Petz recovery channel. On the output support its dual is characterized by $S_{\Phi(\sigma)}\Theta_\sigma^*(A)S_{\Phi(\sigma)}=\Phi(S_\sigma A S_\sigma)$, where $S_\tau=\sqrt\tau$. Extend this dual off that support by $\operatorname{Tr}(\sigma A)(I-P_{\Phi(\sigma)})$. Then
--
--   $$D(\Phi(\rho)\|\Phi(\sigma))=D(\rho\|\sigma)\iff \Phi\text{ is reversible on }\{\rho,\sigma\}\iff \rho=\Theta_\sigma(\Phi(\rho)).$$
--
--   This includes nonfaithful $\rho$ and $\sigma$; no spectral gap or bounded inverse is assumed.
--
--   This result identifies equality in relative-entropy monotonicity with exact common recovery, including degenerate states.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 6, Theorem 1: Petz equivalence, including the degenerate-state extension proved in Appendix 5.1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize traceClosure rankOne productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary traceFirst traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats extendedRelativeEntropyNats ensembleHolevo pureStates finiteEnsembleCapacity)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff ReversibleOn IsometricallyEquivalent
   IsParsevalFrame IsKrausRepresentation)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tensorRankLE)

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

/-- Theorem 1, PDF pp.6–7, including Appendix 5.1, pp.23–25. The reference
may be degenerate. The computed Petz map restricts to output support and
explicitly extends off it by preparing sigma; no bounded inverse is used. -/
theorem petz_threeConditions
    {I J : Type} [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (Phi : Channel I J) (rho sigma : State I)
    (hFinite : extendedRelativeEntropyNats rho.coefficients sigma.coefficients < ⊤) :
    IsTraceClassChannel (petzRecovery Phi.val sigma.coefficients) ∧
    ((extendedRelativeEntropyNats (Phi.val rho.coefficients) (Phi.val sigma.coefficients) =
        extendedRelativeEntropyNats rho.coefficients sigma.coefficients) ↔
      ReversibleOn Phi.val {rho, sigma}) ∧
    (ReversibleOn Phi.val {rho, sigma} ↔
      rho.coefficients = petzRecovery Phi.val sigma.coefficients (Phi.val rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
