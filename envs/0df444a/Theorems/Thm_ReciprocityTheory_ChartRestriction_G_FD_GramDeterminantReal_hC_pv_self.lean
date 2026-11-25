-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_pv_self
-- name    : ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.hC_pv_self
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:17:44.711725+00:00
-- url     : https://prove2.me/theorems/32134556-30af-49fd-95de-8b706a23aef6
-- title:
--   Gram Determinant Real: h C pv self
-- statement:
--   The Gram Determinant Real construction uses the h C pv self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L166-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L166-L171

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

theorem ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.hC_pv_self {n : ℕ} (f : Fin n → Fin r → ℂ) (e : Fin r → ℂ)
    (hA : IsUnit (gramF τ G f).det) :
    hermC τ G (pv τ G f e) (pv τ G f e) = ∑ b, conj (yv τ G f e b) * cv τ G f e b := by sorry
