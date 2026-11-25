-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantNormalForms_hgram_posDef
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.hgram_posDef
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:18:51.109825+00:00
-- url     : https://prove2.me/theorems/ed72e17d-7e54-451d-a8c0-0dbfd7ef4290
-- title:
--   Majorant Normal Forms: hgram pos Def
-- statement:
--   The Majorant Normal Forms construction uses the hgram pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantNormalForms.lean#L146-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantNormalForms.lean#L146-L178

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms
open Matrix NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.hgram_posDef {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    (Matrix.of fun a c => X.Hf x τ (col (mat x τ) a) (col (mat x τ) c)).PosDef := by sorry
