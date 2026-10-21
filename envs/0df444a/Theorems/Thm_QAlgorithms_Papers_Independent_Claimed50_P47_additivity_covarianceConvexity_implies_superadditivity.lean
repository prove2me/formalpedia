-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P47_additivity_covarianceConvexity_implies_superadditivity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P47.additivity_covarianceConvexity_implies_superadditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:34:59.194561+00:00
-- url     : https://prove2.me/theorems/02d0af4f-edda-44bf-917f-9cad2c2dddfc
-- title:
--   Global additivity and covariance convexity imply Gaussian superadditivity
-- statement:
--   Suppose Gaussian entanglement of formation $E_G$ is additive on every pair of physical bipartite Gaussian covariances, and is convex as a function of covariance matrices of every finite mode size. Let $k\ge1$, and partition a finite bipartite collection of modes as $A=\bigcup_{i=1}^k A_i$ and $B=\bigcup_{i=1}^k B_i$, where each pair $A_i|B_i$ has a positive finite total number of modes. For every physical joint covariance $\gamma$, let $[\gamma]_i$ be its principal covariance on $A_i|B_i$. Then
--
--   $$
--   E_G(\gamma)\ge\sum_{i=1}^k E_G([\gamma]_i).
--   $$
--
--   Correlations between different paired subsystems are allowed, and the local mode counts may differ. The two premises are global properties; covariance convexity concerns arithmetic combinations of covariances, rather than mixtures of density operators. This is the finite-family superadditivity property of Eq. (58).
-- source:
--   Gaussian quantum channels, arXiv:quant-ph/0505151v1, PDF p. 17, §5.4, Eq. (61): additivity and covariance convexity imply superadditivity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P47

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P10
  (Phase sigma physicalCovariance pureCovariance thermalCovariance cpMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (PureDensity partialRight boundedUnitaryConjugation dilationReceiver)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

/-- Eisert--Wolf, PDF p.17, (61), iterated to the finite-family form (58):
global additivity together with global covariance convexity implies Gaussian
EoF superadditivity, for arbitrary finite local mode counts on both parties. -/
theorem additivity_covarianceConvexity_implies_superadditivity
    (hadditive : GaussianEoFAdditive) (hconvex : GaussianEoFCovarianceConvex) :
    GaussianEoFSuperadditive := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P47

end
