-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_isMaximal_comap_of_isMaximal_b84c1c04496c
-- name    : P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_isMaximal_comap_of_isMaximal_b84c1c04496c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:51.162322+00:00
-- url     : https://prove2.me/theorems/2ef006f1-e494-4b8e-96d7-fd32aada9111
-- title:
--   P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre is Maximal comap of is Maximal b84c1c04496c: P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre is Maxima
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre is Maximal comap of is Maximal b84c1c04496c construction uses the P2 M Ground Theory Heights  Heights Four B Closed Point Of Generic Fibre is Maximal comap of is Maximal b84c1c04496c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PClosedPointOfGenericFibre.lean#L36-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PClosedPointOfGenericFibre.lean#L36-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsClosedPointGenericFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PClosedPointOfGenericFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain NumberField
open GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre

theorem P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_isMaximal_comap_of_isMaximal_b84c1c04496c (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R]
    [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (M : Ideal R) (hM : M.IsMaximal) :
    (M.comap (algebraMap (𝓞 F) R)).IsMaximal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«ClosedPointOfGenericFibre».«isMaximal_comap_of_isMaximal» := P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_isMaximal_comap_of_isMaximal_b84c1c04496c
