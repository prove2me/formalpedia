-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Unr_unramExt
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Unr.unramExt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:39:42.012791+00:00
-- url     : https://prove2.me/theorems/b632c836-6038-47ae-8bcb-7b7f0d693da2
-- title:
--   Unr: unram Ext
-- statement:
--   The Unr construction uses the unram Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/UnramExt.lean#L17-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/UnramExt.lean#L17-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Unramified.LocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_UnramExt
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
open IsLocalRing Polynomial
open scoped IntermediateField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Unr
open ReciprocityTheory.ChartRestriction.G.Semi.Nb

theorem ReciprocityTheory.ChartRestriction.G.Semi.Unr.unramExt : ReciprocityTheory.ChartRestriction.G.Out.UnramExtSt := by sorry
