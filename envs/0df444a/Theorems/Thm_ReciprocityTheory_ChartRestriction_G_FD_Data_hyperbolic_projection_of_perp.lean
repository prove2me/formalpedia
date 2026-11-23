-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hyperbolic_projection_of_perp
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.hyperbolic_projection_of_perp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:27.700803+00:00
-- url     : https://prove2.me/theorems/f181d686-b5cb-41e5-8563-24f213cce958
-- title:
--   Data: hyperbolic projection of perp
-- statement:
--   The Data construction uses the hyperbolic projection of perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L262-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L262-L265

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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.hyperbolic_projection_of_perp {u : Fin r → ℂ} (hu1 : hermC τ.1 X.Gm u e = 0)
    (hu2 : hermC τ.1 X.Gm u (X.Jp x τ e) = 0) : X.d2pi x τ e u = u := by sorry
