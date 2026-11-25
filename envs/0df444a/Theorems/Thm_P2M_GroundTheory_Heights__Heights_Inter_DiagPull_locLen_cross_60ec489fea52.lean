-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_locLen_cross_60ec489fea52
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagPull_locLen_cross_60ec489fea52
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:31.547363+00:00
-- url     : https://prove2.me/theorems/6b06f3b7-f06e-4245-b7a4-b3cc1fa61c94
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag Pull loc Len cross 60ec489fea52: P2 M Ground Theory Heights  Heights Inter Diag Pull loc Len cross 60ec489fea52
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag Pull loc Len cross 60ec489fea52 construction uses the P2 M Ground Theory Heights  Heights Inter Diag Pull loc Len cross 60ec489fea52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L44-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagPull.lean#L44-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Inter.DiagPull
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagPull_locLen_cross_60ec489fea52 {V : Ideal R} (hV : V.IsPrime) {f g u v : R} (hrel : f * v - g * u ∈ V)
    (p : PrimeSpectrum R) (hVp : V ≤ p.asIdeal) (hu : u ∉ p.asIdeal) (hv : v ∉ p.asIdeal) :
    locLen (R ⧸ (V ⊔ Ideal.span {f})) p = locLen (R ⧸ (V ⊔ Ideal.span {g})) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagPull».«locLen_cross» := P2M_GroundTheory_Heights__Heights_Inter_DiagPull_locLen_cross_60ec489fea52
