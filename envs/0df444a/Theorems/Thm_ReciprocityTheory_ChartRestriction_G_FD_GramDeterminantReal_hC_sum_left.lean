-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_sum_left
-- name    : ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.hC_sum_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:23.721379+00:00
-- url     : https://prove2.me/theorems/952ffbd6-a91b-47ac-bfa8-9dd31bd9db6d
-- title:
--   Gram Determinant Real: h C sum left
-- statement:
--   The Gram Determinant Real construction uses the h C sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L24-L28

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

theorem ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.hC_sum_left {n : ℕ} (f : Fin n → Fin r → ℂ) (w : Fin n → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ b, w b • f b) v = ∑ b, w b * hermC τ G (f b) v := by sorry
