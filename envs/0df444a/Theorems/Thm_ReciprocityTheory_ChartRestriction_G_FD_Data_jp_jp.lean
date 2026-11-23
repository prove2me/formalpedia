-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_jp_jp
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.jp_jp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:06.878985+00:00
-- url     : https://prove2.me/theorems/dd41caf1-7e3d-42a6-9203-981a4b2fccec
-- title:
--   Data: jp jp
-- statement:
--   The Data construction uses the jp jp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L445-L453
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L445-L453

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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.jp_jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.jp x τ (X.jp x τ v) = v := by sorry
