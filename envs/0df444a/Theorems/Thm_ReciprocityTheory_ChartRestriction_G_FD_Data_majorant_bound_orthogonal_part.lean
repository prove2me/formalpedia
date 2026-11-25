-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_majorant_bound_orthogonal_part
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.majorant_bound_orthogonal_part
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:12:29.265416+00:00
-- url     : https://prove2.me/theorems/a2582e3b-816e-54ff-8836-e6a0c34777d5
-- title:
--   Data: majorant bound orthogonal part
-- statement:
--   The Data construction uses the majorant bound orthogonal part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantBoundOrthogonalPart.lean#L45-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantBoundOrthogonalPart.lean#L45-L67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantBoundOrthogonalPart
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
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.majorant_bound_orthogonal_part (ξ : Fin r → E) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ) (κ : ℝ)
    (hδ : ∀ u ∈ X.Uz x ξ, ∀ τ, X.maj x τ (δ τ (u τ) • emb τ.1 ξ) ≤ κ ^ 2 * X.maj x τ (u τ))
    (τ : X.Ψ) (w : Fin r → ℂ) (hw1 : hermC τ.1 X.Gm w (emb τ.1 ξ) = 0)
    (hw2 : hermC τ.1 X.Gm w (X.Jp x τ (emb τ.1 ξ)) = 0) :
    X.maj x τ (δ τ w • emb τ.1 ξ) ≤ κ ^ 2 * X.maj x τ w := by sorry
