-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P24_mueller_jones_semigroup
-- name    : QAlgorithms.Papers.Independent.Intake100.P24.mueller_jones_semigroup
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:17:37.456954+00:00
-- url     : https://prove2.me/theorems/63109455-292a-41be-b37e-9b118cdbf435
-- title:
--   Mueller–Jones maps form a semigroup
-- statement:
--   A Mueller–Jones map is a pair $(\Phi,V)$ in which $\Phi$ is complex-linear, completely positive and doubly contracting, $VV^\dagger\le I$, and $\Phi-(X\mapsto VXV^\dagger)$ is positive. The composition is
--
--   $$(\Phi,V)\circ(\Psi,W)=(\Phi\circ\Psi,VW).$$
--
--   The composition of two such maps is again a Mueller–Jones map, and this operation is associative. Thus these abstract maps form the semigroup stated in (55), with the right-hand map acting first.
-- source:
--   Quantum features of macroscopic fields. Entropy and dynamics, arXiv:1904.06170v1, PDF p. 9, §VI.B, (55): Mueller–Jones semigroup

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P24

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

namespace QAlgorithms.Papers.Independent.Intake100.P24

local instance : MeasurableSpace PolarizationMatrix := borel PolarizationMatrix

local instance : BorelSpace PolarizationMatrix := ⟨rfl⟩

/-- arXiv:1904.06170v1 PDF p.9, (55): admissible Mueller–Jones maps are
closed under the displayed composition, and that composition is associative.
It asserts no physical realization or surjectivity onto optical devices. -/
theorem mueller_jones_semigroup (P Q R : MuellerJonesPair)
    (hP : IsMuellerJones P) (hQ : IsMuellerJones Q) (hR : IsMuellerJones R) :
    IsMuellerJones (muellerJonesCompose P Q) ∧
      muellerJonesCompose (muellerJonesCompose P Q) R =
        muellerJonesCompose P (muellerJonesCompose Q R) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P24

end
