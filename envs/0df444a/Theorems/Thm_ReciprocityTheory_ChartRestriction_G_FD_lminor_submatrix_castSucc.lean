-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_lminor_submatrix_castSucc
-- name    : ReciprocityTheory.ChartRestriction.G.FD.lminor_submatrix_castSucc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:21:15.456165+00:00
-- url     : https://prove2.me/theorems/53c0578f-5a26-458e-8acf-8db1591f4ea9
-- title:
--   FD: lminor submatrix cast Succ
-- statement:
--   The FD construction uses the lminor submatrix cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L13-L17

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

theorem ReciprocityTheory.ChartRestriction.G.FD.lminor_submatrix_castSucc {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) :
    lminor (A.submatrix Fin.castSucc Fin.castSucc) i = lminor A i.castSucc := by sorry
