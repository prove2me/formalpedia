-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_jp_sub
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.jp_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:22.24771+00:00
-- url     : https://prove2.me/theorems/0ec266cc-8ac1-4d4a-ab9d-276ce12a513d
-- title:
--   Data: jp sub
-- statement:
--   The Data construction uses the jp sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L438-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L438-L443

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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.jp_sub (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.jp x τ (u - v) = X.jp x τ u - X.jp x τ v := by sorry
