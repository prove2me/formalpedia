-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_sub_left
-- name    : ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.hC_sub_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:07.847226+00:00
-- url     : https://prove2.me/theorems/e0a265e8-6272-48de-b563-653020657cf0
-- title:
--   Gram Determinant Real: h C sub left
-- statement:
--   The Gram Determinant Real construction uses the h C sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L19-L20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

theorem ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.hC_sub_left (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by sorry
