-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_X__ddfde4c79f12
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_X__ddfde4c79f12
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:44.712476+00:00
-- url     : https://prove2.me/theorems/97e2caba-b6b8-4937-97d1-eef7976e3eed
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry is Multi Homog X  ddfde4c79f12: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry is Multi Homog X  ddfde4c79f12
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry is Multi Homog X  ddfde4c79f12 construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry is Multi Homog X  ddfde4c79f12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsMultiHomogX.lean#L33-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsMultiHomogX.lean#L33-L49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogIdealChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogX
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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_X__ddfde4c79f12 [DecidableEq K] (b : K) (i : ι b) :
    IsMultiHomog (X ⟨b, i⟩ : MRing ι) (Pi.single b 1) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«isMultiHomog_X'» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_X__ddfde4c79f12
