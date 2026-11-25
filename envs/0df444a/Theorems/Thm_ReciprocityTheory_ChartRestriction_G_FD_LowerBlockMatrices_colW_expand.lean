-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_colW_expand
-- name    : ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices.colW_expand
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:23:18.083843+00:00
-- url     : https://prove2.me/theorems/bd0510da-f82c-4f44-ae01-67bc33f8b72c
-- title:
--   Lower Block Matrices: col W expand
-- statement:
--   The Lower Block Matrices construction uses the col W expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LowerBlockMatrices.lean#L69-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LowerBlockMatrices.lean#L69-L103

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

theorem ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices.colW_expand (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 : Frame X.Ψ r) {x0 : Frame X.Ψ r}
    (hortho : X.IsOrtho x0) (τ : X.Ψ) (hdet0 : (mat x0 τ).det ≠ 0) (b : Fin X.p0) :
    col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) =
      ∑ b', Amat X h1 z0 x0 τ b' b • col (mat x0 τ) (Fin.castLE X.p0_le b') +
        ∑ a, Bmat X h1 z0 x0 τ a b • col (mat x0 τ) (kap X.p0_le a) := by sorry
