-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_comb_orth_zero
-- name    : ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.comb_orth_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:03.695953+00:00
-- url     : https://prove2.me/theorems/76f0a3ba-90fb-400e-bdda-82298c2c4bce
-- title:
--   Gram Determinant Real: comb orth zero
-- statement:
--   The Gram Determinant Real construction uses the comb orth zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L67-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L67-L77

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
variable {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ)

theorem ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.comb_orth_zero {n : ℕ} (f : Fin n → Fin r → ℂ) (hA : IsUnit (gramF τ G f).det)
    (w : Fin n → ℂ) (h : ∀ d, hermC τ G (∑ b, w b • f b) (f d) = 0) : ∑ b, w b • f b = 0 := by sorry
