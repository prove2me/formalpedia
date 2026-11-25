-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_VT_val_mem
-- name    : ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace.VT.val_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:31:55.498314+00:00
-- url     : https://prove2.me/theorems/31f665bb-1a57-4c3b-9b62-e8cee426e7ec
-- title:
--   VT: val mem
-- statement:
--   The VT construction uses the val mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealTangentSpace.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealTangentSpace.lean#L35-L36

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealTangentSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (z : Frame X.Ψ r) (ξ : Fin r → E)

theorem ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace.VT.val_mem {z : Frame X.Ψ r} {ξ : Fin r → E} (u : VT (X := X) z ξ) : u.val ∈ X.Uz z ξ := by sorry
