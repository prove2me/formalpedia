-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_eSec_th__1cd1bf797aec
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_eSec_th__1cd1bf797aec
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:18:25.526484+00:00
-- url     : https://prove2.me/theorems/f1195c07-20ef-49c9-9070-9b237270db68
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Geo Tor e Sec th  1cd1bf797aec: P2 M Reciprocity Theory Chart Restriction G Geo Tor e Sec th  1cd1bf797aec
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Geo Tor e Sec th  1cd1bf797aec construction uses the P2 M Reciprocity Theory Chart Restriction G Geo Tor e Sec th  1cd1bf797aec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ExtVCat.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ExtVCat.lean#L49-L53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExtVCat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_eSec_th__1cd1bf797aec (I : thK) : eSec (G3 G) ≫ thφ G (x3 G) I = eSec G := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Geo».«Tor».«eSec_thφ» := P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_eSec_th__1cd1bf797aec
