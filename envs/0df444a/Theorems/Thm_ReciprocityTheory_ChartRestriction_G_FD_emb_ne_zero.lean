-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_emb_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.G.FD.emb_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:14.008861+00:00
-- url     : https://prove2.me/theorems/027474dc-e57e-4f4c-b04c-44254a065c0c
-- title:
--   FD: emb ne zero
-- statement:
--   The FD construction uses the emb ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L475-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L475-L482

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

theorem ReciprocityTheory.ChartRestriction.G.FD.emb_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    {u : Fin r → E} (hu : u ≠ 0) : Data.emb τ u ≠ 0 := by sorry
