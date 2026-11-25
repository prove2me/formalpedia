-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_flowMat_isom_real
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants.flowMat_isom_real
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:13:47.982615+00:00
-- url     : https://prove2.me/theorems/2779808f-018e-4130-8f46-404fc3009c9c
-- title:
--   Flow Matrix Majorants: flow Mat isom real
-- statement:
--   The Flow Matrix Majorants construction uses the flow Mat isom real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMatrixMajorants.lean#L78-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMatrixMajorants.lean#L78-L96

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

theorem ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants.flowMat_isom_real (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (t : ℝ)
    (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (X.flowMat ξ τ t) u) (Matrix.mulVec (X.flowMat ξ τ t) v) =
      hermC τ.1 X.Gm u v := by sorry
