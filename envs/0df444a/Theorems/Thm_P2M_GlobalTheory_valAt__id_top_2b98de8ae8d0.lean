-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__id_top_2b98de8ae8d0
-- name    : P2M_GlobalTheory_valAt__id_top_2b98de8ae8d0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:58.907539+00:00
-- url     : https://prove2.me/theorems/a7af3585-3a75-4e31-b2c6-fb5263151ce0
-- title:
--   P2 M Global Theory val At  id top 2b98de8ae8d0: P2 M Global Theory val At  id top 2b98de8ae8d0
-- statement:
--   The P2 M Global Theory val At  id top 2b98de8ae8d0 construction uses the P2 M Global Theory val At  id top 2b98de8ae8d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L182-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L182-L186

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
variable {X Y : Scheme.{0}}

theorem P2M_GlobalTheory_valAt__id_top_2b98de8ae8d0 (a : ℂ) :
    valAt' (𝟙 (Sp ℂ)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) = a := by sorry

alias «GlobalTheory».«valAt'_id_top» := P2M_GlobalTheory_valAt__id_top_2b98de8ae8d0
