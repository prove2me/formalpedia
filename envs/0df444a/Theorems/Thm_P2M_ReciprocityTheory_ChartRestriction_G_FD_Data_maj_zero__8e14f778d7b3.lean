-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_zero__8e14f778d7b3
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_zero__8e14f778d7b3
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:47.833242+00:00
-- url     : https://prove2.me/theorems/2e51cf86-04de-5685-bd6b-c6bb274832f7
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Data maj zero  8e14f778d7b3: P2 M Reciprocity Theory Chart Restriction G FD Data maj zero  8e14f778d7b3
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Data maj zero  8e14f778d7b3 construction uses the P2 M Reciprocity Theory Chart Restriction G FD Data maj zero  8e14f778d7b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentSubOneMajorantBound.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentSubOneMajorantBound.lean#L48-L50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
variable {x : Frame X.Ψ r} {τ : X.Ψ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_zero__8e14f778d7b3 (hself : ∀ v, X.Hf x τ v v = (X.maj x τ v : ℂ)) : X.maj x τ 0 = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«Data».«maj_zero'» := P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_zero__8e14f778d7b3
