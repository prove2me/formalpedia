-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermitian_pairing_e_Je
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.hermitian_pairing_e_Je
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:38.234587+00:00
-- url     : https://prove2.me/theorems/01511fbe-4dbb-4423-859a-c53136a7ef48
-- title:
--   Data: hermitian pairing e Je
-- statement:
--   The Data construction uses the hermitian pairing e Je property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L245-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentOnHyperbolicComplement.lean#L245-L245

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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.hermitian_pairing_e_Je (hx : x ∈ X.dom) : hermC τ.1 X.Gm e (X.Jp x τ e) = X.d2q x τ e := by sorry
