-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_Neg_eq
-- name    : ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices.Neg_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:50.086655+00:00
-- url     : https://prove2.me/theorems/76e9de63-e93e-4aba-a0b1-adb6ec13a7da
-- title:
--   Lower Block Matrices: Neg eq
-- statement:
--   The Lower Block Matrices construction uses the Neg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LowerBlockMatrices.lean#L57-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LowerBlockMatrices.lean#L57-L67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BlockIdentityExpansion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowerBlockMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices.Neg_eq (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 x0 : Frame X.Ψ r) (τ : X.Ψ) (u : Fin X.p0 → ℂ) :
    Neg X x0 τ (∑ b, u b • col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b)) =
      ∑ a, ‖(Bmat X h1 z0 x0 τ *ᵥ u) a‖ ^ 2 := by sorry
