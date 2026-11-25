-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_iso_pos
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.Hf_iso_pos
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:11:56.622018+00:00
-- url     : https://prove2.me/theorems/7705a32a-1071-53f8-a2b4-dc54ec7f79fb
-- title:
--   Data: Hf iso pos
-- statement:
--   The Data construction uses the Hf iso pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L370-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L370-L383

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

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.Hf_iso_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) {e : Fin r → ℂ} (he : e ≠ 0)
    (hiso : hermC τ.1 X.Gm e e = 0) : 0 < (X.Hf x τ e e).re := by sorry
