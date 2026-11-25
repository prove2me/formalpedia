-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Jp_add__70eb83
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.Jp_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:17:00.247715+00:00
-- url     : https://prove2.me/theorems/70eb8305-07a2-4bd8-915e-6a64de41c702
-- title:
--   Data: Jp add
-- statement:
--   The Data construction uses the Jp add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L141-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L141-L145

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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.Jp_add (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.Jp x τ (u + v) = X.Jp x τ u + X.Jp x τ v := by sorry
