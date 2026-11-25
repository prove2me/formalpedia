-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_Hf_add_left
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants.Hf_add_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:14:18.873522+00:00
-- url     : https://prove2.me/theorems/dd03be2b-5c80-5f80-aa7d-71c1d408e9d5
-- title:
--   Flow Matrix Majorants: Hf add left
-- statement:
--   The Flow Matrix Majorants construction uses the Hf add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMatrixMajorants.lean#L98-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMatrixMajorants.lean#L98-L104

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants
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
open ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants
open MajorantConjugateTransfer
variable {r : ℕ} (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ)

theorem ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants.Hf_add_left (x : Frame X.Ψ r) (u u' w : Fin r → ℂ) :
    X.Hf x τ (u + u') w = X.Hf x τ u w + X.Hf x τ u' w := by sorry
