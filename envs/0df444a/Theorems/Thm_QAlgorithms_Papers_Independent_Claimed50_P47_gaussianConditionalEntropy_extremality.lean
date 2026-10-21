-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P47_gaussianConditionalEntropy_extremality
-- name    : QAlgorithms.Papers.Independent.Claimed50.P47.gaussianConditionalEntropy_extremality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:33:20.531988+00:00
-- url     : https://prove2.me/theorems/5efa212a-db6a-4b31-8473-b41699593e34
-- title:
--   Gaussian states maximize quantum conditional entropy at fixed moments
-- statement:
--   Let $A$ and $B$ be finite collections of bosonic modes, with a positive total number of modes. Let $\rho$ and $\widetilde\rho$ be normalized positive trace-class states on the full joint oscillator Hilbert space. Suppose that $\rho$ is Gaussian and that both states have the same finite first moments $d$ and doubled covariance matrix $\gamma$, in units $\hbar=1$. Write $\rho_A$ and $\widetilde\rho_A$ for their reductions to $A$, and use natural logarithms in the von Neumann entropy $S$. All four joint and marginal entropies are finite, and
--
--   $$
--   S(\widetilde\rho)-S(\widetilde\rho_A)\le S(\rho)-S(\rho_A).
--   $$
--
--   Thus second moments determine a Gaussian upper bound on this conditional entropy, with the paper's convention $S(A|B)=S(AB)-S(A)$. Pure Gaussian factors are included.
-- source:
--   Gaussian quantum channels, arXiv:quant-ph/0505151v1, PDF p. 8, §3.3, Eq. (23): Gaussian conditional-entropy extremality (abstract seed)

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

/-- Eisert--Wolf, PDF pp.7--8, (22)--(23): conditional entropy S(AB)-S(A)
is maximized by the Gaussian counterpart with the same first and second moments.
Finiteness is concluded before real-valued subtraction; pure Gaussian factors
are allowed. Relative-entropy monotonicity is not a hypothesis. -/
theorem gaussianConditionalEntropy_extremality
    {A B : Type} [Fintype A] [Fintype B]
    (hmodes : 0 < Fintype.card A + Fintype.card B)
    (rho tilde : State (Occupation A × Occupation B))
    (d : Quadratures (A ⊕ B) → ℝ)
    (gamma : Matrix (Quadratures (A ⊕ B)) (Quadratures (A ⊕ B)) ℝ)
    (hphysical : physicalCovariance gamma (canonicalForm (A ⊕ B)))
    (hGaussian : HasBipartiteGaussianCharacteristic rho.coefficients d gamma)
    (hmoments : HasBipartiteMoments tilde.coefficients d gamma) :
    extendedEntropyNats rho.coefficients < ⊤ ∧
    extendedEntropyNats tilde.coefficients < ⊤ ∧
    extendedEntropyNats (partialRight rho.coefficients) < ⊤ ∧
    extendedEntropyNats (partialRight tilde.coefficients) < ⊤ ∧
    (extendedEntropyNats tilde.coefficients).toReal -
        (extendedEntropyNats (partialRight tilde.coefficients)).toReal ≤
      (extendedEntropyNats rho.coefficients).toReal -
        (extendedEntropyNats (partialRight rho.coefficients)).toReal := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P47

end
