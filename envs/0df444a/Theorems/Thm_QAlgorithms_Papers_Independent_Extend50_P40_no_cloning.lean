-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_no_cloning
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.no_cloning
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:53:10.029728+00:00
-- url     : https://prove2.me/theorems/03a09163-d2dc-48fe-a655-20da0762cf3a
-- title:
--   §I.B: no-cloning theorem (seed topic pinned to its explicit theorem)
-- statement:
--   Let $d\ge2$. A deterministic quantum operation is one fixed completely positive trace-preserving map from a $d$-level system to two such systems. There is no such map $T$ satisfying, for every normalized pure vector $\psi$,
--
--   $$
--   T(|\psi\rangle\langle\psi|)=|\psi\rangle\langle\psi|\otimes|\psi\rangle\langle\psi|.
--   $$
--
--   This is the impossibility of perfect universal 1-to-2 cloning, including any initially input-independent blank and environment through the channel model.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 3, §I.B: no-cloning theorem (seed topic pinned to its explicit theorem)

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

/-- I.B, PDF p.3: no fixed deterministic quantum operation perfectly clones all pure states.
Pure marginals are equivalent to this product target by Appendix A p.31. -/
theorem no_cloning (d : ℕ) (hd : 2 ≤ d) :
    ¬ ∃ T : Superop (Fin d) (Fin d × Fin d), IsChannel T ∧
      ∀ psi : EuclideanSpace ℂ (Fin d), ‖psi‖ = 1 →
        T (pureDensity psi) = Matrix.kronecker (pureDensity psi) (pureDensity psi) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
