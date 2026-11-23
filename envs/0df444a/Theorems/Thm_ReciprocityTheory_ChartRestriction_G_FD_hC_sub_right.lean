-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_sub_right
-- name    : ReciprocityTheory.ChartRestriction.G.FD.hC_sub_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:41.054879+00:00
-- url     : https://prove2.me/theorems/6f66f303-fc70-4d42-bb73-6189e0ecc084
-- title:
--   FD: h C sub right
-- statement:
--   The FD construction uses the h C sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L30-L32

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
variable {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

theorem ReciprocityTheory.ChartRestriction.G.FD.hC_sub_right (u v v' : Fin r → ℂ) :
    hermC τ G u (v - v') = hermC τ G u v - hermC τ G u v' := by sorry
