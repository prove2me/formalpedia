-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_asymmetry_filter
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.asymmetry_filter
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:23:07.272787+00:00
-- url     : https://prove2.me/theorems/9499b53b-f1fc-4368-b441-2c0497a487c5
-- title:
--   §VI.A.2 Eq.(103): asymmetric optimal cloning by a beam-splitter filter
-- statement:
--   For $1/2\le T\le1$, apply $K_T=(2T-1)I+2(1-T)|\Psi^-\rangle\langle\Psi^-|$ to the second clone and anti-clone of the symmetric qubit cloner. It is a Kraus contraction, $K_T^\dagger K_T\le I$, with positive input-independent success probability. After normalization its universal fidelities satisfy
--
--   $$
--   \sqrt{(1-F_A)(1-F_B)}=\tfrac12-(1-F_A)-(1-F_B).
--   $$
--
--   At T=1 both fidelities are 5/6; at T=1/2 they are 1 and 1/2. The filter is generally not an idempotent projector. The minus sign in the source’s (102) is retained through the explicit BH state.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 26, §VI.A.2 Eq.(103): asymmetric optimal cloning by a beam-splitter filter

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

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeHilbert ModeOperator IsModeDensity FockWeylSystem)

open QAlgorithms.Papers.Independent.Renew46.P41
  (coherentProduct NormalizedCoherent IsReducedDensity FockCanonicalAction
   ModeUnitary twoModeAmplifierQuadratures modeMixingQuadratures embeddedOpticalBeam
   displacedThermal cloneNoise cloneFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentProjector)

/-- VI.A.2, PDF p.26 Eqs.(102)–(103): positive contraction branch and
strictly positive postselection. Eq.(102) has a MINUS before its Pauli sum.
The normalized filtered state saturates Eq.(23), including both source endpoints. -/
theorem asymmetry_filter (T : ℝ) (h0 : 1 / 2 ≤ T) (h1 : T ≤ 1) :
    (1 - (asymmetryFilter T)ᴴ * asymmetryFilter T).PosSemidef ∧
    ∃ p fA fB : ℝ, 0 < p ∧ p ≤ 1 ∧
      (∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 → ‖filteredOutput T psi‖ ^ 2 = p ∧
        let out := ((Real.sqrt p : ℂ)⁻¹) • filteredOutput T psi
        ‖out‖ = 1 ∧ pureFidelity psi (cloneMarginalA out) = fA ∧ pureFidelity psi (cloneMarginalB out) = fB) ∧
      Real.sqrt ((1 - fA) * (1 - fB)) = 1 / 2 - (1 - fA) - (1 - fB) ∧
      (T = 1 → fA = 5 / 6 ∧ fB = 5 / 6) ∧ (T = 1 / 2 → fA = 1 ∧ fB = 1 / 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
