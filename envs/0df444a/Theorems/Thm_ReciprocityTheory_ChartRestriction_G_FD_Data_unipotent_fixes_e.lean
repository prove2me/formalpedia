-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_unipotent_fixes_e
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.unipotent_fixes_e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:16:51.304801+00:00
-- url     : https://prove2.me/theorems/f5bd52ff-d432-5013-93b5-cd0bc46fc49c
-- title:
--   Data: unipotent fixes e
-- statement:
--   The Data construction uses the unipotent fixes e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L296-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L296-L298

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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.unipotent_fixes_e : Matrix.mulVec (X.d2n x τ e δ) e = e := by sorry
