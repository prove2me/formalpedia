-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantNormalForms_gram_normal
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.gram_normal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:24:42.808856+00:00
-- url     : https://prove2.me/theorems/c0b6f563-a502-5bef-b27f-07cc47e700fa
-- title:
--   Majorant Normal Forms: gram normal
-- statement:
--   The Majorant Normal Forms construction uses the gram normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantNormalForms.lean#L263-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantNormalForms.lean#L263-L325

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

theorem ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.gram_normal {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) {B : Matrix (Fin r) (Fin r) ℂ}
    (hBd : B.det ≠ 0) (hBt : ∀ a c : Fin r, c < a → B a c = 0)
    (hB : ∀ a c, X.Hf x τ (col (mat x τ * B) a) (col (mat x τ * B) c) = if a = c then 1 else 0) :
    gram τ.1 X.Gm (mat x τ * B) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by sorry
