-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermC_ppos_self
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.hermC_ppos_self
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:21.486273+00:00
-- url     : https://prove2.me/theorems/8459425e-7d98-4333-8919-edf42329b50e
-- title:
--   Data: herm C ppos self
-- statement:
--   The Data construction uses the herm C ppos self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L244-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L244-L251

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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.hermC_ppos_self (τ : X.Ψ) (x : Frame X.Ψ r) (u : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) u = ∑ a, ∑ b, hermC τ.1 X.Gm u (X.colP x τ a) *
      (X.gramPos x τ)⁻¹ a b * conj (hermC τ.1 X.Gm u (X.colP x τ b)) := by sorry
