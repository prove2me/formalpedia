-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_dv_orth
-- name    : ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.dv_orth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:34.163841+00:00
-- url     : https://prove2.me/theorems/5d06b9e8-296b-447c-be02-0e9f256f3912
-- title:
--   Gram Determinant Real: dv orth
-- statement:
--   The Gram Determinant Real construction uses the dv orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L60-L65

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

theorem ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.dv_orth (hA : IsUnit (gramF τ G f).det)
    (hA' : IsUnit (gramF τ G (fun a : Fin n => f a.castSucc)).det) (d : Fin n) :
    hermC τ G (dv τ G f e) (f d.castSucc) = 0 := by sorry
