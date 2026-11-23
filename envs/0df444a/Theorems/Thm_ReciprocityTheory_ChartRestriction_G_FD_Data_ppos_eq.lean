-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_eq
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.ppos_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:34:41.42311+00:00
-- url     : https://prove2.me/theorems/4819b524-353a-4c8e-9094-58bc468292b5
-- title:
--   Data: ppos eq
-- statement:
--   The Data construction uses the ppos eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L227-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L227-L228

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.ppos_eq (x : Frame X.Ψ r) (τ : X.Ψ) (u : Fin r → ℂ) : X.ppos x τ u =
    ∑ a, (∑ b, hermC τ.1 X.Gm u (X.colP x τ b) * (X.gramPos x τ)⁻¹ b a) • X.colP x τ a := by sorry
