-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_psgn_eq_one
-- name    : ReciprocityTheory.ChartRestriction.G.FD.psgn_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:51:43.52038+00:00
-- url     : https://prove2.me/theorems/ec88f80c-58af-4397-9ea1-2478ee9264a5
-- title:
--   FD: psgn eq one
-- statement:
--   The FD construction uses the psgn eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L195-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L195-L200

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

theorem ReciprocityTheory.ChartRestriction.G.FD.psgn_eq_one {p0 i : ℕ} (h : i ≤ p0) : psgn p0 i = 1 := by sorry
