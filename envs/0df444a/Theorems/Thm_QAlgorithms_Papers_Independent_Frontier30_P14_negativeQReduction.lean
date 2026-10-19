-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P14_negativeQReduction
-- name    : QAlgorithms.Papers.Independent.Frontier30.P14.negativeQReduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:23:27.229983+00:00
-- url     : https://prove2.me/theorems/eafef137-d8e1-4334-8495-9c10c9bb7bbb
-- title:
--   Negative-q decomposition with explicit output swap
-- statement:
--   Let $U$ implement a full two-mode canonical matrix $A$, let $\sigma$ be a Gaussian environmental density, and let $q=|A_{11}|^2-|A_{12}|^2<0$. Let $\Xi$ be the vacuum-preserving swap of the identical Fock factors. There exist local Gaussian unitaries $S_a,S_b,R_b$, a bounded standard amplifier coupling $V$ of gain $1-q>1$, and $|c|=1$, such that
--
--   $$U=c\,\Xi(S_a\otimes S_b)V(I\otimes R_b).$$
--
--   The density $\sigma'=R_b\sigma R_b^\dagger$ is Gaussian. For every input density $\rho$, the type-correct output identity is
--
--   $$E_{U,\sigma}(\rho)\otimes I_b
--   =\Xi\bigl(I_a\otimes S_b F_{V,\sigma'}(\rho)S_b^\dagger\bigr)\Xi.$$
--
--   This identifies the receiver with the amplifier’s weak environmental output through the specified swap. The identity factors are bounded operators and are never supplied as trace-class channel inputs.
-- source:
--   Degradability of Bosonic Gaussian channels, arXiv:quant-ph/0603257v4, PDF p. 6, §III (14), Appendix A.3 (A16)-(A17)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

noncomputable section

open scoped BigOperators NNReal ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace QAlgorithms.Papers.Independent.Frontier30.P14

/-- Section III (14), Appendix A.3 (A16)-(A17), PDF pp.4,6: negative-q maps
reduce to the weak complement of gain 1-q. The swap is explicit on the joint
unitary and on the amplified output identity. No identity operator is passed
through a trace-class channel. The implementer equality allows a scalar phase. -/
theorem negativeQReduction (U : (Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ)))
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hcanonical : Canonical U A)
    (sigma : State ℕ) (hgaussian : GaussianDensity sigma.coefficients)
    (hnegative : characteristicQ A < 0) :
    ∃ (Sa Sb Rin : (Hilbert ℕ ≃ₗᵢ[ℂ] Hilbert ℕ)) (V : (Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ))) (phase : ℂ),
      GaussianUnitary Sa ∧ GaussianUnitary Sb ∧ GaussianUnitary Rin ∧
      Canonical V (standardMatrix (1 - characteristicQ A)) ∧ Complex.normSq phase = 1 ∧
      GaussianDensity (boundedUnitaryConjugation Rin sigma.coefficients) ∧
      (∀ i j, unitaryCoeff U i j = phase *
        composeKernel (productCoeff (unitaryCoeff Sa) (unitaryCoeff Sb))
          (composeKernel (unitaryCoeff V)
            (productCoeff (identityCoeff ℕ) (unitaryCoeff Rin))) (i.2, i.1) j) ∧
      (∀ rho : State ℕ,
        productCoeff (dilationReceiver U sigma.coefficients rho.coefficients) (identityCoeff ℕ) =
          swapCoefficients (productCoeff (identityCoeff ℕ)
            (boundedUnitaryConjugation Sb (weakComplement V (boundedUnitaryConjugation Rin sigma.coefficients) rho.coefficients)))) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P14

end
