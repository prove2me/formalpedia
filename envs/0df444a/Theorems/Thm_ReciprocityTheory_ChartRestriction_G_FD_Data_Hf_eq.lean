-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_eq
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.Hf_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:56.410347+00:00
-- url     : https://prove2.me/theorems/d098eecd-0328-417e-8168-ba4f64cc7567
-- title:
--   Data: Hf eq
-- statement:
--   The Data construction uses the Hf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnitaryComplementMoveOfIsotropic.lean#L55-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnitaryComplementMoveOfIsotropic.lean#L55-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowFixesComplementOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.Hf_eq (x : Frame X.Ψ r) (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    X.Hf x τ u w = hermC τ.1 X.Gm u ((2 : ℂ) • X.ppos x τ w - w) := by sorry
