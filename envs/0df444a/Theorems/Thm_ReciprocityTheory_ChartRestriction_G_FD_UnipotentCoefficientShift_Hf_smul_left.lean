-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_Hf_smul_left
-- name    : ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift.Hf_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:56.787665+00:00
-- url     : https://prove2.me/theorems/2dd6412b-09fa-4662-af80-57c7012173d0
-- title:
--   Unipotent Coefficient Shift: Hf smul left
-- statement:
--   The Unipotent Coefficient Shift construction uses the Hf smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentCoefficientShift.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentCoefficientShift.lean#L55-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift
open NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} {X : Data E r}

theorem ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift.Hf_smul_left (z : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf z τ (k • u) w = k * X.Hf z τ u w := by sorry
