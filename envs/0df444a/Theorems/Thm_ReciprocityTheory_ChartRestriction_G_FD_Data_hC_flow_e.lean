-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hC_flow_e
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.hC_flow_e
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:12:25.305995+00:00
-- url     : https://prove2.me/theorems/0f5f726b-3329-4362-acb7-21d0de0170bf
-- title:
--   Data: h C flow e
-- statement:
--   The Data construction uses the h C flow e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowFixesComplementOfIsotropic.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowFixesComplementOfIsotropic.lean#L46-L48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowFixesComplementOfIsotropic
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
variable (ξ : Fin r → E) (τ : X.Ψ)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.hC_flow_e (hiso : hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = 0) (s : ℂ) (v : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (X.flowMat ξ τ s) v) (emb τ.1 ξ) = hermC τ.1 X.Gm v (emb τ.1 ξ) := by sorry
