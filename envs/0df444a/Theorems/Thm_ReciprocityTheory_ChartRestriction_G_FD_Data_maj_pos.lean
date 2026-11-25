-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
-- name    : ReciprocityTheory.ChartRestriction.G.FD.Data.maj_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:33.765805+00:00
-- url     : https://prove2.me/theorems/8d4c6832-4437-4d55-b4f0-b898dec21460
-- title:
--   Data: maj pos
-- statement:
--   The Data construction uses the maj pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajPos.lean#L75-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajPos.lean#L75-L264

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
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
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.Data.maj_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) {v : Fin r → ℂ} (hv : v ≠ 0) :
    0 < X.maj x τ v := by sorry
