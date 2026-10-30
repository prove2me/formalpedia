-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P38_pureStateEntropyVarianceDuality
-- name    : QAlgorithms.Papers.Independent.Bridge50.P38.pureStateEntropyVarianceDuality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:45:15.751679+00:00
-- url     : https://prove2.me/theorems/1cf754fe-966b-4b30-b7f4-3db689f27fd6
-- title:
--   Pure-state relative entropy and information-variance duality
-- statement:
--   Let $|\psi_{ABC}\rangle$ be a unit vector on three nonempty finite-dimensional complex systems. Let $\rho_{AB}$ and $\rho_{AC}$ be its partial traces, and let $\rho_B$ and $\rho_C$ be their respective marginals. With relative entropy $D$ in bits and information variance $V$ in bits squared,
--
--   $$D(\rho_{AB}\|I_A\otimes\rho_B)=-D(\rho_{AC}\|I_A\otimes\rho_C),\qquad V(\rho_{AB}\|I_A\otimes\rho_B)=V(\rho_{AC}\|I_A\otimes\rho_C).$$
--
--   Every marginal is computed from the same supplied pure state. The lemma packages both dualities; the source credits prior use in Hayashi–Tomamichel [17] and supplies its own proof.
-- source:
--   Decoding quantum information via the Petz recovery map, arXiv:1504.04449v4, PDF p. 21, lemma-A.2

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P38

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Bridge50.P38

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

open QAlgorithms.Papers.Independent.Information100.P63 (normalQuantile)

open QAlgorithms.Papers.Independent.Dependency50.P36
  (relativeEntropyFinite pairInformationVariance)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (columnProjector pinch marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification singleUseInformation coherentInformation)

open QAlgorithms.Papers.Independent.Gap48.P23 (CompletelyPositive)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- PDF pp.21–22, Lemma A.2: BOTH relative-entropy and variance duality,
with every marginal constructed from the same normalized pure state.
The source credits prior use in Hayashi–Tomamichel [17]. -/
theorem pureStateEntropyVarianceDuality [Nonempty A] [Nonempty B] [Nonempty C]
    (psi : EuclideanSpace ℂ (A × B × C)) (hpsi : ‖psi‖ = 1) :
    relativeEntropyFinite (marginalAB (pureDensity psi))
        (Matrix.kronecker (1 : Matrix A A ℂ) (traceLeft (marginalAB (pureDensity psi)))) =
      -relativeEntropyFinite (marginalAC (pureDensity psi))
        (Matrix.kronecker (1 : Matrix A A ℂ) (traceLeft (marginalAC (pureDensity psi)))) ∧
    pairInformationVariance (marginalAB (pureDensity psi))
        (Matrix.kronecker (1 : Matrix A A ℂ) (traceLeft (marginalAB (pureDensity psi)))) =
      pairInformationVariance (marginalAC (pureDensity psi))
        (Matrix.kronecker (1 : Matrix A A ℂ) (traceLeft (marginalAC (pureDensity psi)))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P38

end
