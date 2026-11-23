-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_posDef_of_posSemidef_det
-- name    : ReciprocityTheory.ChartRestriction.G.FD.posDef_of_posSemidef_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:49:00.68519+00:00
-- url     : https://prove2.me/theorems/7f9d7a70-88f3-4c4e-8d74-ad6e45d5f03a
-- title:
--   FD: pos Def of pos Semidef det
-- statement:
--   The FD construction uses the pos Def of pos Semidef det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L9-L11

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

theorem ReciprocityTheory.ChartRestriction.G.FD.posDef_of_posSemidef_det {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (hd : A.det ≠ 0) : A.PosDef := by sorry
