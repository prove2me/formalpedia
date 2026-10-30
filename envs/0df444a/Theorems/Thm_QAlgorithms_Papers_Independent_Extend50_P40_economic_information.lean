-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_economic_information
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.economic_information
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:18:43.023253+00:00
-- url     : https://prove2.me/theorems/b6c8ba47-2931-452f-a73b-0d514b387bf8
-- title:
--   §IV.B.2 Eq.(82): information from the economical BB84 attack
-- statement:
--   For the specified economical BB84 attack, let $0\le\theta<\pi/2$. Alice’s raw bit is uniform, bases have been sifted, and Bob and Eve measure X. With binary entropy $H$ in bits and $I(p)=1-H(p)$, the actual normalized joint law gives
--
--   $$
--   I_{AB}=I((1+\cos\theta)/2),\quad I_{AE}=I((1+\sin\theta)/2),\quad I_{BE}=I((1+\sin\theta\cos\theta)/2)<I_{AB}.
--   $$
--
--   Consequently the displayed raw-information rate I_AB−min(I_AE,I_BE) is positive whenever D=(1−cosθ)/2<1/2, including D=0. This is a calculation for the specified attack and measurement, not an unrestricted QKD security statement.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 21, §IV.B.2 Eq.(82): information from the economical BB84 attack

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

/-- IV.B.2, PDF p.21 Eq.(82) and footnote 27: actual specified attack and X
measurement. The displayed raw rate stays positive for D<1/2, including D=0. -/
theorem economic_information (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta < Real.pi / 2) :
    (∀ a b e, 0 ≤ economicLaw theta a b e) ∧
    (∑ a, ∑ b, ∑ e, economicLaw theta a b e) = 1 ∧
    infoAB (economicLaw theta) = binaryInformation ((1 + Real.cos theta) / 2) ∧
    infoAE (economicLaw theta) = binaryInformation ((1 + Real.sin theta) / 2) ∧
    infoBE (economicLaw theta) = binaryInformation ((1 + Real.sin theta * Real.cos theta) / 2) ∧
    infoBE (economicLaw theta) < infoAB (economicLaw theta) ∧
    0 < rawRate (infoAB (economicLaw theta)) (infoAE (economicLaw theta)) (infoBE (economicLaw theta)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
