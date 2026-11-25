-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_unipotent_shift_self_pairing
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.unipotent_shift_self_pairing
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:54.006726+00:00
-- url     : https://prove2.me/theorems/78535de9-26bf-4f8c-9f95-b25241c2695f
-- title:
--   Data: unipotent shift self pairing
-- statement:
--   The Data construction uses the unipotent shift self pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L292-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L292-L294

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
variable (x : Frame X.Ψ r) (τ : X.Ψ) (e : Fin r → ℂ) (δ : (Fin r → ℂ) →ₗ[ℂ] ℂ)
variable {x τ e}
variable (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0) (hq : X.d2q x τ e ≠ 0)
include hx he hq

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.unipotent_shift_self_pairing : hermC τ.1 X.Gm (X.d2z x τ e δ) (X.d2z x τ e δ) =
    X.d2q x τ e * δ (X.d2z x τ e δ) := by sorry
