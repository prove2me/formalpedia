-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_colZ
-- name    : ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices.colZ
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:00.989403+00:00
-- url     : https://prove2.me/theorems/9511162d-6b8e-468e-bfc3-4ffe6fa528d6
-- title:
--   Lower Block Matrices: col Z
-- statement:
--   The Lower Block Matrices construction uses the col Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LowerBlockMatrices.lean#L118-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LowerBlockMatrices.lean#L118-L126

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

theorem ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices.colZ (x0 : Frame X.Ψ r) (Z : X.Coord) (τ : X.Ψ) (b : Fin X.p0) :
    col (mat (X.xZ x0 Z) τ) (Fin.castLE X.p0_le b) =
      col (mat x0 τ) (Fin.castLE X.p0_le b) + ∑ a, Z τ a b • col (mat x0 τ) (kap X.p0_le a) := by sorry
