-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P14_positiveQReduction
-- name    : QAlgorithms.Papers.Independent.Frontier30.P14.positiveQReduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:22:57.697874+00:00
-- url     : https://prove2.me/theorems/37145417-f3c9-4c78-83a6-675061144fa4
-- title:
--   Positive-q decomposition into a standard coupling and local Gaussian unitaries
-- statement:
--   Let $U$ implement the full two-mode canonical matrix $A$ and let $\sigma$ be a Gaussian environmental density. Put $q=|A_{11}|^2-|A_{12}|^2$ and suppose $q>0$, $q\ne1$. There exist local Gaussian unitaries $S_a,S_b,R_b$, a bounded standard coupling $V_q$ implementing (11) when $0<q<1$ or (12) when $q>1$, and a scalar $c$ with $|c|=1$, such that
--
--   $$U=c(S_a\otimes S_b)V_q(I\otimes R_b).$$
--
--   Writing $\sigma'=R_b\sigma R_b^\dagger$, the state $\sigma'$ is Gaussian and, for every input density,
--
--   $$E_{U,\sigma}(\rho)=S_a E_{V_q,\sigma'}(\rho)S_a^\dagger.$$
--
--   The local transformations include the oscillator phase rotations allowed by the source. They and the phase are chosen independently of $\rho$. The channel equality is exact; only the implementer equality allows the physically immaterial scalar phase.
-- source:
--   Degradability of Bosonic Gaussian channels, arXiv:quant-ph/0603257v4, PDF p. 5, §III (13), Appendix A.1-A.2, (A9)-(A13), pp.5-6

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace QAlgorithms.Papers.Independent.Frontier30.P14

/-- Section III (13), Appendix A.1-A.2, PDF pp.3,5-6: the two positive-q
regimes share one decomposition. Single-mode phase rotations are retained.
(A9) is stated modulo a scalar phase; its induced channel equality is exact. -/
theorem positiveQReduction (U : (Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ)))
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hcanonical : Canonical U A)
    (sigma : State ℕ) (hgaussian : GaussianDensity sigma.coefficients)
    (hpositive : 0 < characteristicQ A) (hone : characteristicQ A ≠ 1) :
    ∃ (Sa Sb Rin : (Hilbert ℕ ≃ₗᵢ[ℂ] Hilbert ℕ)) (V : (Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ))) (phase : ℂ),
      GaussianUnitary Sa ∧ GaussianUnitary Sb ∧ GaussianUnitary Rin ∧
      Canonical V (standardMatrix (characteristicQ A)) ∧ Complex.normSq phase = 1 ∧
      GaussianDensity (boundedUnitaryConjugation Rin sigma.coefficients) ∧
      (∀ i j, unitaryCoeff U i j = phase *
        composeKernel (productCoeff (unitaryCoeff Sa) (unitaryCoeff Sb))
          (composeKernel (unitaryCoeff V)
            (productCoeff (identityCoeff ℕ) (unitaryCoeff Rin))) i j) ∧
      (∀ rho : State ℕ, dilationReceiver U sigma.coefficients rho.coefficients =
        boundedUnitaryConjugation Sa (dilationReceiver V (boundedUnitaryConjugation Rin sigma.coefficients) rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P14

end
