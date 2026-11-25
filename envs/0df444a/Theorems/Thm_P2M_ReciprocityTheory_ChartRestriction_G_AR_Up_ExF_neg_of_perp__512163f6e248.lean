-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_neg_of_perp__512163f6e248
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_neg_of_perp__512163f6e248
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:13:47.857547+00:00
-- url     : https://prove2.me/theorems/8418eae2-f171-5c69-bade-101bc280f712
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Ex F neg of perp  512163f6e248: P2 M Reciprocity Theory Chart Restriction G AR Up Ex F neg of perp  512163f6e248
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Ex F neg of perp  512163f6e248 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Ex F neg of perp  512163f6e248 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustFStatementPfB.lean#L12-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustFStatementPfB.lean#L12-L141

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_neg_of_perp__512163f6e248 {x : Frame X.Ψ r} (τ : X.Ψ) (hA : (X.gramPos x τ).PosDef) {e : Fin r → ℂ}
    (he : e ≠ 0) (hperp : ∀ b, hermC τ.1 X.Gm e (X.colP x τ b) = 0) :
    (hermC τ.1 X.Gm e e).re < 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«ExF».«neg_of_perp'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_neg_of_perp__512163f6e248
