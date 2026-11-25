-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_posDef_of_lminor
-- name    : ReciprocityTheory.ChartRestriction.G.FD.posDef_of_lminor
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:21:26.115804+00:00
-- url     : https://prove2.me/theorems/b4740747-378e-4b0e-9e78-989f0960dc73
-- title:
--   FD: pos Def of lminor
-- statement:
--   The FD construction uses the pos Def of lminor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L22-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L22-L78

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

theorem ReciprocityTheory.ChartRestriction.G.FD.posDef_of_lminor : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.IsHermitian →
    (∀ i : Fin (n + 1), 0 < (lminor A i).re) → A.PosDef
  := by sorry
