-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramFlowTransform_det_flw
-- name    : ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform.det_flw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:21.53081+00:00
-- url     : https://prove2.me/theorems/4d5df47f-9405-458e-95ea-386cf7dcf7db
-- title:
--   Gram Flow Transform: det flw
-- statement:
--   The Gram Flow Transform construction uses the det flw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramFlowTransform.lean#L44-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramFlowTransform.lean#L44-L57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramFlowTransform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E}

theorem ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform.det_flw (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ)
    (hA : IsUnit (gramF τ G f).det) : (gramF τ G (flw α e τ G f)).det =
      (gramF τ G f).det * (1 + (α + conj α) * GramDeterminantReal.mt τ G f e) := by sorry
