-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P47_gaussianEoF_minimumOutputEntropy
-- name    : QAlgorithms.Papers.Independent.Claimed50.P47.gaussianEoF_minimumOutputEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:34:34.409232+00:00
-- url     : https://prove2.me/theorems/76ea8768-80f0-4be0-9477-666e139c1140
-- title:
--   Gaussian entanglement of formation and minimum output entropy
-- statement:
--   Let $T$ be a Gaussian channel on $n\ge1$ modes and fix a pure Gaussian dilation with environmental covariance $\gamma_0$ and symplectic transformation $S$. For a physical input covariance $\gamma$, put $\gamma'=S(\gamma\oplus\gamma_0)S^{\mathsf T}$. Let $E_G$ denote Gaussian entanglement of formation across the output--environment cut, and let $S(T(\eta))$ denote the entropy of the centered Gaussian output with covariance $X\eta X^{\mathsf T}+Y$. With all entropies in nats,
--
--   $$
--   E_G(\gamma')=\inf_{\substack{\widetilde\gamma\ \mathrm{physical}\\\widetilde\gamma\le\gamma}}S(T(\widetilde\gamma)),
--   \qquad
--   \nu_{1,G}(T)=\inf_{\gamma\ \mathrm{physical}}E_G\!\left(S(\gamma\oplus\gamma_0)S^{\mathsf T}\right).
--   $$
--
--   Here covariance order is positive semidefinite order, and $\nu_{1,G}$ is the infimum of output von Neumann entropy over all Gaussian input states. These identities retain the fixed-average information in the first formula and then relate its unconstrained infimum to minimum output entropy. Pure inputs are allowed and there is no energy constraint.
-- source:
--   Gaussian quantum channels, arXiv:quant-ph/0505151v1, PDF p. 16, §5.4, Eqs. (56)–(57): Gaussian EoF and minimum output entropy

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

/-- Eisert--Wolf, PDF p.16, both (56) and (57). Gaussian EoF of the dilated
fixed-average covariance is the least output entropy over physical covariances
below that average. The unrestricted Gaussian minimum is the infimum of these
EoFs. Alpha=1, no input energy constraint, pure boundary inputs included. -/
theorem gaussianEoF_minimumOutputEntropy {n : ℕ} (hn : 0 < n)
    (Phi : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ →
      Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (X Y : Matrix (Quadratures (Fin n)) (Quadratures (Fin n)) ℝ)
    (hGaussian : IsGaussianChannel Phi X Y) (D : PureGaussianDilation Phi X Y) :
    (∀ gamma : Matrix (Quadratures (Fin n)) (Quadratures (Fin n)) ℝ,
      physicalCovariance gamma (canonicalForm (Fin n)) →
      gaussianEoF (dilatedCovariance D gamma) =
        ⨅ small : {small : Matrix (Quadratures (Fin n)) (Quadratures (Fin n)) ℝ //
          physicalCovariance small (canonicalForm (Fin n)) ∧ CovarianceBelow small gamma},
          gaussianOutputEntropy X Y small.val) ∧
    gaussianMinimumOutputEntropy X Y =
      ⨅ gamma : {gamma : Matrix (Quadratures (Fin n)) (Quadratures (Fin n)) ℝ //
          physicalCovariance gamma (canonicalForm (Fin n))},
        gaussianEoF (dilatedCovariance D gamma.val) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P47

end
