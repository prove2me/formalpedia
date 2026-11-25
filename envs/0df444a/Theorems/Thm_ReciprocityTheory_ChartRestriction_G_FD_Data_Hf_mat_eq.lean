-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_mat_eq
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.Hf_mat_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:19.211615+00:00
-- url     : https://prove2.me/theorems/25b4bf90-0d52-4978-aa54-fb7530988745
-- title:
--   Data: Hf mat eq
-- statement:
--   The Data construction uses the Hf mat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantBoundOrthogonalPart.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantBoundOrthogonalPart.lean#L38-L40

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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.Hf_mat_eq {x x' : Frame X.Ψ r} {τ : X.Ψ} (h : mat x τ = mat x' τ) (v w : Fin r → ℂ) :
    X.Hf x τ v w = X.Hf x' τ v w := by sorry
