-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_det_gramF_real
-- name    : ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.det_gramF_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:01.35558+00:00
-- url     : https://prove2.me/theorems/501e29bf-5081-414c-a0e1-a2f8cab1498e
-- title:
--   Gram Determinant Real: det gram F real
-- statement:
--   The Gram Determinant Real construction uses the det gram F real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L154-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L154-L164

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
variable {τ G} (hG : ∀ a b, τ (G b a) = conj (τ (G a b)))
include hG

theorem ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.det_gramF_real {n : ℕ} (f : Fin n → Fin r → ℂ) : (gramF τ G f).det.im = 0 := by sorry
