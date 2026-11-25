-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_ringKrullDim_le_of_isIntegral__578cfa688125
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_ringKrullDim_le_of_isIntegral__578cfa688125
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:15:06.068667+00:00
-- url     : https://prove2.me/theorems/97b7a07c-da8f-442f-b959-79bc0c2eec89
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry ring Krull Dim le of is Integral  578cfa688125: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry ring Krull Dim le of is Inte
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry ring Krull Dim le of is Integral  578cfa688125 construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry ring Krull Dim le of is Integral  578cfa688125 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/StepTStB.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/StepTStB.lean#L11-L16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemSec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_ringKrullDim_le_of_isIntegral__578cfa688125 {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«ringKrullDim_le_of_isIntegral'» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_ringKrullDim_le_of_isIntegral__578cfa688125
