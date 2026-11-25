-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantNormalForms_exists_normal
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.exists_normal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:23:52.102833+00:00
-- url     : https://prove2.me/theorems/07169c67-5136-5bd4-92a6-3e9ff767d0cf
-- title:
--   Majorant Normal Forms: exists normal
-- statement:
--   The Majorant Normal Forms construction uses the exists normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantNormalForms.lean#L180-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantNormalForms.lean#L180-L250

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

theorem ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.exists_normal {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    ∃ B : Matrix (Fin r) (Fin r) ℂ, B.det ≠ 0 ∧ (∀ a c : Fin r, c < a → B a c = 0) ∧
      ∀ a c : Fin r, X.Hf x τ (col (mat x τ * B) a) (col (mat x τ * B) c) =
        if a = c then 1 else 0 := by sorry
