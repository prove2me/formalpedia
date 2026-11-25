-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_gramF_comb
-- name    : ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.gramF_comb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:11.821095+00:00
-- url     : https://prove2.me/theorems/5da266bb-aea5-5b2c-a2f4-99b233b3e9ec
-- title:
--   Gram Determinant Real: gram F comb
-- statement:
--   The Gram Determinant Real construction uses the gram F comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L137-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramDeterminantReal.lean#L137-L146

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

theorem ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.gramF_comb {n : ℕ} (f : Fin n → Fin r → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    gramF τ G (fun a => ∑ b, M b a • f b) = Mᵀ * gramF τ G f * M.map conj := by sorry
