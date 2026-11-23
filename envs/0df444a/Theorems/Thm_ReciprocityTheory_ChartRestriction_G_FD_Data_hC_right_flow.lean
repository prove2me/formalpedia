-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hC_right_flow
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.hC_right_flow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:33.413729+00:00
-- url     : https://prove2.me/theorems/cc2c8e07-a9ad-49dd-8a87-df3592aa613d
-- title:
--   Data: h C right flow
-- statement:
--   The Data construction uses the h C right flow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowFixesComplementOfIsotropic.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowFixesComplementOfIsotropic.lean#L54-L56

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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.hC_right_flow (s : ℂ) (y v : Fin r → ℂ) (hy : hermC τ.1 X.Gm y (emb τ.1 ξ) = 0) :
    hermC τ.1 X.Gm y (Matrix.mulVec (X.flowMat ξ τ s) v) = hermC τ.1 X.Gm y v := by sorry
