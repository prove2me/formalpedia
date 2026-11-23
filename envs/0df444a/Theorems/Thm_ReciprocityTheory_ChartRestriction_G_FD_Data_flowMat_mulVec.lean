-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_flowMat_mulVec
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.flowMat_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:37.311975+00:00
-- url     : https://prove2.me/theorems/e10930ce-e964-4a60-881b-ad354d32c961
-- title:
--   Data: flow Mat mul Vec
-- statement:
--   The Data construction uses the flow Mat mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMatMulVec.lean#L61-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMatMulVec.lean#L61-L72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.flowMat_mulVec (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (v : Fin r → ℂ) :
    Matrix.mulVec (X.flowMat ξ τ s) v =
      v + (-(I * X.c τ * s) * hermC τ.1 X.Gm v (emb τ.1 ξ)) • emb τ.1 ξ := by sorry
