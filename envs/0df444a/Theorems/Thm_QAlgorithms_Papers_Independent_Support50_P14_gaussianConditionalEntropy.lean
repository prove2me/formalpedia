-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P14_gaussianConditionalEntropy
-- name    : QAlgorithms.Papers.Independent.Support50.P14.gaussianConditionalEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:30:34.690185+00:00
-- url     : https://prove2.me/theorems/c575c5a0-f3cb-445e-8103-f07c113bf239
-- title:
--   Unnumbered conditional-entropy rederivation
-- statement:
--   Let $A$ and $B$ be nonempty finite collections of full oscillator modes, and let $\rho_{AB}$ be a normalized density with finite complete moments. Let $\rho^G_{AB}$ be a Gaussian density with the same symmetric covariance, allowing different first moments. All four entropies of the joint states and their $A$ marginals are finite. With $S$ measured in nats,
--
--   $$S(\rho_{AB})-S(\rho_A)\le S(\rho^G_{AB})-S(\rho^G_A).$$
--
--   Thus Gaussian states maximize conditional entropy at fixed covariance. The sign is opposite to the functional $f(\rho)=S(\rho_A)-S(\rho_{AB})$ used by Lemma 1.
-- source:
--   Extremality of Gaussian quantum states, arXiv:quant-ph/0509154v1, PDF p. 2, Unnumbered conditional-entropy rederivation

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

noncomputable section

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P14

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel boundedUnitaryConjugation)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

/-- Conditional entropy rederived on PDF p.2: S(AB)-S(A) is MAXIMIZED by the
Gaussian counterpart. All four entropies are finite; toReal never hides infinity.
The input and comparator means may differ by local displacements. -/
theorem gaussianConditionalEntropy {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho rhoG : State (Occupation (A ⊕ B)))
    (d dG : InterleavedQuadrature (A ⊕ B) → ℝ) (gamma : OscillatorCovariance (A ⊕ B))
    (hmoments : CompleteMoments rho.coefficients d gamma)
    (hgaussian : GaussianAt rhoG.coefficients dG gamma) :
    extendedEntropyNats rho.coefficients < ⊤ ∧
    extendedEntropyNats rhoG.coefficients < ⊤ ∧
    extendedEntropyNats (marginalFirst rho.coefficients) < ⊤ ∧
    extendedEntropyNats (marginalFirst rhoG.coefficients) < ⊤ ∧
    (extendedEntropyNats rho.coefficients).toReal -
      (extendedEntropyNats (marginalFirst rho.coefficients)).toReal ≤
    (extendedEntropyNats rhoG.coefficients).toReal -
      (extendedEntropyNats (marginalFirst rhoG.coefficients)).toReal := by sorry

end QAlgorithms.Papers.Independent.Support50.P14

end
