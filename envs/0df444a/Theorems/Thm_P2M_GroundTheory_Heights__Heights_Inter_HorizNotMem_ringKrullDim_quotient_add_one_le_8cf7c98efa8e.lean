-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_HorizNotMem_ringKrullDim_quotient_add_one_le_8cf7c98efa8e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_HorizNotMem_ringKrullDim_quotient_add_one_le_8cf7c98efa8e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:13.403804+00:00
-- url     : https://prove2.me/theorems/899931c6-218d-4d6d-982a-a32383476bc1
-- title:
--   P2 M Ground Theory Heights  Heights Inter Horiz Not Mem ring Krull Dim quotient add one le 8cf7c98efa8e: P2 M Ground Theory Heights  Heights Inter Horiz Not Mem ring Krull Dim quotient add one le 8cf7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Horiz Not Mem ring Krull Dim quotient add one le 8cf7c98efa8e construction uses the P2 M Ground Theory Heights  Heights Inter Horiz Not Mem ring Krull Dim quotient add one le 8cf7c98efa8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PHorizNotMem.lean#L12-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PHorizNotMem.lean#L12-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PHorizNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Inter_HorizNotMem_ringKrullDim_quotient_add_one_le_8cf7c98efa8e {R : Type*} [CommRing R] {W₀ W : Ideal R}
    [hW₀ : W₀.IsPrime] [hW : W.IsPrime] (hlt : W₀ < W) :
    ringKrullDim (R ⧸ W) + 1 ≤ ringKrullDim (R ⧸ W₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«HorizNotMem».«ringKrullDim_quotient_add_one_le» := P2M_GroundTheory_Heights__Heights_Inter_HorizNotMem_ringKrullDim_quotient_add_one_le_8cf7c98efa8e
