-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_conjugate_conjugate__4a5ffdebff34
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_conjugate_conjugate__4a5ffdebff34
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:37:32.134119+00:00
-- url     : https://prove2.me/theorems/c0900469-7d85-4d1f-8908-2bb251c15dd8
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Data conjugate conjugate  4a5ffdebff34: P2 M Reciprocity Theory Chart Restriction G FD Data conjugate conjugate  4a5ffdebff34
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Data conjugate conjugate  4a5ffdebff34 construction uses the P2 M Reciprocity Theory Chart Restriction G FD Data conjugate conjugate  4a5ffdebff34 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ConjugateConjugate.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ConjugateConjugate.lean#L52-L55

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
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_conjugate_conjugate__4a5ffdebff34 (φ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«Data».«conjugate_conjugate'» := P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_conjugate_conjugate__4a5ffdebff34
