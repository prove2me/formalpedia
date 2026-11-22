-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:49.586031+00:00
-- url     : https://prove2.me/theorems/0d2766f4-a681-4ae7-a324-759e83209948
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Geo Tor Is Cub face  8d4277abb339: P2 M Reciprocity Theory Chart Restriction G Geo Tor Is Cub face  8d4277abb339
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Geo Tor Is Cub face  8d4277abb339 construction uses the P2 M Reciprocity Theory Chart Restriction G Geo Tor Is Cub face  8d4277abb339 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CubeVal.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CubeVal.lean#L30-L31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
variable {A U : Type} [CommGroup A] [CommGroup U]
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub
variable {θ : A → A → A → U} (h : IsCub θ)
include h

theorem P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339 (x y : A) : θ x 1 y = 1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Geo».«Tor».«IsCub».«face₂» := P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
