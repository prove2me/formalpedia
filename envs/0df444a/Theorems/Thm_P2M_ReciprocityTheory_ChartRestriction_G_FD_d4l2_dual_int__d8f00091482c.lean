-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_d4l2_dual_int__d8f00091482c
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_d4l2_dual_int__d8f00091482c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:11.872648+00:00
-- url     : https://prove2.me/theorems/b60885b5-e36b-4ccd-a85d-d14a1a9bf996
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD d4l2 dual int  d8f00091482c: P2 M Reciprocity Theory Chart Restriction G FD d4l2 dual int  d8f00091482c
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD d4l2 dual int  d8f00091482c construction uses the P2 M Reciprocity Theory Chart Restriction G FD d4l2 dual int  d8f00091482c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ConjugateConjugate.lean#L33-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ConjugateConjugate.lean#L33-L46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_d4l2_dual_int__d8f00091482c (t : E) (h : ∀ γ : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (t * γ) = k) :
    IsIntegral ℤ (((NumberField.discr E).natAbs : E) * t) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«d4l2_dual_int'» := P2M_ReciprocityTheory_ChartRestriction_G_FD_d4l2_dual_int__d8f00091482c
