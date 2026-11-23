-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Jp_Jp__4f74ff
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.Jp_Jp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:27.458817+00:00
-- url     : https://prove2.me/theorems/4f74ff64-9c7b-4fef-a20b-6dd4ddd55444
-- title:
--   Data: Jp Jp
-- statement:
--   The Data construction uses the Jp Jp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L163-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L163-L169

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
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
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.Jp_Jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.Jp x τ (X.Jp x τ v) = v := by sorry
