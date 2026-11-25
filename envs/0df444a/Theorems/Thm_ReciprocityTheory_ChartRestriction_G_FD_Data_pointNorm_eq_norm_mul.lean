-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_pointNorm_eq_norm_mul
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.pointNorm_eq_norm_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:12:18.969355+00:00
-- url     : https://prove2.me/theorems/233a8289-3797-5d82-8ae8-10619dbd4078
-- title:
--   Data: point Norm eq norm mul
-- statement:
--   The Data construction uses the point Norm eq norm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentVectorEqSmulComponent.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentVectorEqSmulComponent.lean#L18-L20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentVectorEqSmulComponent
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
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.pointNorm_eq_norm_mul (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ) (z : Frame X.Ψ r) :
    X.pnorm la G z = ‖G z‖ * X.pnorm la (fun _ => (1 : ℂ)) z := by sorry
