-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P01_coherent_information_calculus
-- name    : QAlgorithms.Papers.Independent.Intake100.P01.coherent_information_calculus
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:56:23.066008+00:00
-- url     : https://prove2.me/theorems/c6b7ee54-258b-4495-9b0e-8d667f99648a
-- title:
--   Coherent information identities and superadditivity, eqs.(65)–(69)
-- statement:
--   For every normalized density matrix on finite nonzero registers $A_1,A_2,B$, define $I(X\rangle Y)=S(Y)-S(XY)$ and $I(X\rangle Y\mid Z)=S(Y\mid Z)-S(XY\mid Z)$, with bit entropies of the computed marginals. Then
--   $$I(A_1\rangle B\mid A_2)=I(A_1\rangle BA_2),$$
--   $$I(A_1A_2\rangle B)=I(A_2\rangle B)+I(A_1\rangle B\mid A_2),$$
--   $$I(A_1\rangle B)+I(A_2\rangle B)\le I(A_1A_2\rangle B),\qquad I(A_1\rangle B)\le I(A_1\rangle B\mid A_2).$$
--   These identities and inequalities allow genuinely quantum conditioning and retain negative coherent information; no purity or classical-flag assumption is imposed.
-- source:
--   Quantum state merging and negative information, arXiv:quant-ph/0512247v1, PDF p. 17, Coherent information identities and superadditivity, eqs.(65)–(69)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P01

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply finTransport referenceInformation)

open QAlgorithms.Papers.Independent.Bridge50.P40
  (RankMergingCode OneWayMergingCode mergingFidelity SourceProtocolAchievable)

open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRA marginalRB motherTarget motherOutput sourceCopies swap mutualInformation)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Advance50.P29 (weakTypicalProjector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.17, (66),(67),(69), and the stated monotonicity under conditioning.
All marginals are computed from one arbitrary normalized mixed state.
Coherent information is not truncated at zero. -/
theorem coherent_information_calculus {A1 A2 B : Type}
    [Fintype A1] [Fintype A2] [Fintype B] [Nonempty A1] [Nonempty A2] [Nonempty B]
    (rho : Matrix (A1 × (A2 × B)) (A1 × (A2 × B)) ℂ)
    (hrho : IsDensityMatrix rho) :
    let rhoA1B : Matrix (A1 × B) (A1 × B) ℂ :=
      fun p q => ∑ a2, rho (p.1,(a2,p.2)) (q.1,(a2,q.2))
    let i1 := vnEntropy (traceLeft (traceLeft rho)) - vnEntropy rhoA1B
    let i2 := vnEntropy (traceLeft (traceLeft rho)) - vnEntropy (traceLeft rho)
    let i12 := vnEntropy (traceLeft (traceLeft rho)) - vnEntropy rho
    quantumConditionedCoherent rho = vnEntropy (traceLeft rho) - vnEntropy rho ∧
    i12 = i2 + quantumConditionedCoherent rho ∧
    i1 + i2 ≤ i12 ∧ i1 ≤ quantumConditionedCoherent rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P01

end
