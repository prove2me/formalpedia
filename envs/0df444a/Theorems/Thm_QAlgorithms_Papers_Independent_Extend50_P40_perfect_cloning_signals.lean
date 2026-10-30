-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_perfect_cloning_signals
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.perfect_cloning_signals
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:54:40.427671+00:00
-- url     : https://prove2.me/theorems/5d769cee-9d30-461d-be56-ae45b979ab57
-- title:
--   §I.C.1: Herbert thought experiment distinguishes remote basis choices
-- statement:
--   In Herbert’s singlet experiment, hypothetical perfect clones give Bob $\rho_x=(|++\rangle\langle++|+|--\rangle\langle--|)/2$ or $\rho_z=(|00\rangle\langle00|+|11\rangle\langle11|)/2$, according to Alice’s basis. Computational-basis outcome $01$ has probabilities
--
--   $$
--   \Pr_{\rho_x}(01)=\tfrac14,\qquad\Pr_{\rho_z}(01)=0,\qquad\rho_x\ne\rho_z.
--   $$
--
--   Thus the hypothetical cloning rule would reveal a remote basis choice with positive probability; no physical perfect cloning channel is asserted to exist.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 3, §I.C.1: Herbert thought experiment distinguishes remote basis choices

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P40

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open MeasureTheory Filter

open scoped Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)

open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- I.C.1, PDF p.3: Herbert's two hypothetical cloned mixtures give different
probabilities on outcome 01, without assuming existence of a physical perfect cloner. -/
theorem perfect_cloning_signals :
    let rx := (1 / 2 : ℂ) •
      (pureDensity (tensorVec (equator 0) (equator 0)) +
       pureDensity (tensorVec (equator Real.pi) (equator Real.pi)))
    let rz := (1 / 2 : ℂ) • (pureDensity (ket ((0, 0) : (Fin 2 × Fin 2))) + pureDensity (ket ((1, 1) : (Fin 2 × Fin 2))))
    densityProb rx (0, 1) = 1 / 4 ∧ densityProb rz (0, 1) = 0 ∧ rx ≠ rz := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
