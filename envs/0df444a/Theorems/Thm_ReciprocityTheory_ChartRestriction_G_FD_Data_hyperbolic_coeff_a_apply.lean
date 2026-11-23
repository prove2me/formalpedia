-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hyperbolic_coeff_a_apply
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.hyperbolic_coeff_a_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:35.659997+00:00
-- url     : https://prove2.me/theorems/a0d14191-d0d4-4f78-a96c-89c38445016a
-- title:
--   Data: hyperbolic coeff a apply
-- statement:
--   The Data construction uses the hyperbolic coeff a apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L215-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L215-L216

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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.hyperbolic_coeff_a_apply (v : Fin r → ℂ) :
    X.d2a x τ e v = (X.d2q x τ e)⁻¹ * hermC τ.1 X.Gm v (X.Jp x τ e) := by sorry
