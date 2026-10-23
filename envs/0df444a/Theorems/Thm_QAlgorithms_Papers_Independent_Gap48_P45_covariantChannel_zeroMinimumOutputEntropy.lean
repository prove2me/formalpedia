-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_covariantChannel_zeroMinimumOutputEntropy
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.covariantChannel_zeroMinimumOutputEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:06:26.341403+00:00
-- url     : https://prove2.me/theorems/0e6d1349-c91c-48bc-8c12-138c25791366
-- title:
--   Corollary 5: zero minimum output entropy for compact irreducibly covariant channels
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. For unit vectors $\eta_k$, write $G_{P,\eta}(X)=\sum_{k,l}\langle\eta_l|\eta_k\rangle P_kXP_l$. Let $H_A=H_B$ have positive finite dimension. Let a compact topological group $G$ act by a continuous irreducible unitary representation $V_g$, and assume $\Phi(V_g\rho V_g^*)=V_g\Phi(\rho)V_g^*$ for every $g$ and state $\rho$. Define $H_{\min}(\Phi)=\min_\rho H(\Phi(\rho))$. Then
--
--   $$H_{\min}(\Phi)=0\iff\Phi\text{ is unitarily equivalent to }G_{P,\eta}\text{ for some orthogonal resolution and unit vectors }\eta_k.$$
--
--   This result characterizes zero minimum output entropy for irreducibly covariant channels.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 21, Corollary 5: zero minimum output entropy for compact irreducibly covariant channels

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

/-- Corollary 5, PDF p.21: compact-group covariance under a continuous
irreducible unitary representation, on one nonzero finite-dimensional space. -/
theorem covariantChannel_zeroMinimumOutputEntropy
    {I G : Type} [Fintype I] [Nonempty I]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (Phi : Channel I I) (V : G → (Hilbert I ≃ₗᵢ[ℂ] Hilbert I))
    (hAction : IrreducibleUnitaryAction V)
    (hCovariant : ∀ g (rho : State I),
      Phi.val (conjugateCoeff (V g).toLinearIsometry.toContinuousLinearMap rho.coefficients) =
        conjugateCoeff (V g).toLinearIsometry.toContinuousLinearMap (Phi.val rho.coefficients)) :
    minimumOutputEntropy Phi.val = 0 ↔
      ∃ (K : Type) (_ : Countable K) (P : K → (Hilbert I →L[ℂ] Hilbert I)),
        OrthogonalResolution P ∧ HasGramNormalForm Phi.val P False := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
