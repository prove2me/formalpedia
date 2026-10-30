-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P02_li_one_shot_test
-- name    : QAlgorithms.Papers.Independent.Bridge50.P02.li_one_shot_test
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:44:19.551229+00:00
-- url     : https://prove2.me/theorems/6381543d-4f23-4c90-aecc-2e4d1e717d75
-- title:
--   Proposition 1: Li’s one-shot test existence
-- statement:
--   Let $\rho,\sigma$ be faithful density matrices on a nonzero finite-dimensional complex Hilbert space. For every $L>0$, there exists one effect $0\le T\le I$ such that
--   $$\operatorname{Tr}\rho(I-T)\le\langle\Omega_\rho,P_{[0,L)}(\Delta_{\rho\mid\sigma})\Omega_\rho\rangle,\qquad\operatorname{Tr}\sigma T\le L^{-1}.$$
--   Here $\Omega_\rho=\sqrt\rho$, $\Delta_{\rho\mid\sigma}(X)=\rho X\sigma^{-1}$, and $P_{[0,L)}$ is its spectral projector onto the half-open interval that excludes $L$.
--
--   The same test satisfies both bounds. This states the existence result attributed to Li, without endorsing the faulty particular construction in Appendix C.
-- source:
--   Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more, arXiv:1510.04682v4, PDF p. 14, Proposition 1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P02

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate positiveMatrixRpow modularMatrix modularQuadratic resolventOverlap petzOverlap
    finiteRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower testingBeta)

open QAlgorithms.Papers.Independent.Information100.P58 (normalQuantile)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Proposition 1 (Li), PDF p.14, (3.14): one test satisfying BOTH bounds;
the interval [0,L) excludes L. The defective Appendix C construction is not asserted. -/
theorem li_one_shot_test [Nonempty I] (rho sigma : Mat I)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hsigma : QAlgorithms.IsDensityMatrix sigma)
    (hfaithfulRho : rho.PosDef) (hfaithfulSigma : sigma.PosDef) (L : ℝ) (hL : 0 < L) :
    ∃ T : Mat I, QAlgorithms.IsEffect T ∧
      evaluate rho (1-T) ≤ modularQuadratic rho (modularLowProjector rho sigma L) ∧
      evaluate sigma T ≤ L⁻¹ := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P02

end
