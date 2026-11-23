-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hyperbolic_projection_apply
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.hyperbolic_projection_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:41.022078+00:00
-- url     : https://prove2.me/theorems/0fb17fc3-81f6-494b-82ea-a88559d0cdec
-- title:
--   Data: hyperbolic projection apply
-- statement:
--   The Data construction uses the hyperbolic projection apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L218-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L218-L219

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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.hyperbolic_projection_apply (v : Fin r → ℂ) :
    X.d2pi x τ e v = v - X.d2a x τ e v • e - X.d2b x τ e v • X.Jp x τ e := by sorry
