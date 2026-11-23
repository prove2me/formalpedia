-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_conj_mem_iff
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.conj_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:27.393147+00:00
-- url     : https://prove2.me/theorems/bc44b49c-bed6-480b-acc6-eaa5feca0e8c
-- title:
--   Data: conj mem iff
-- statement:
--   The Data construction uses the conj mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ConjugateConjugate.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ConjugateConjugate.lean#L57-L58

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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.conj_mem_iff (φ : E →+* ℂ) : ComplexEmbedding.conjugate φ ∈ X.Ψ ↔ φ ∉ X.Ψ := by sorry
