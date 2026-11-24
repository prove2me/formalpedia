-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_freeQuot_rank_span
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.freeQuot_rank_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:16.904424+00:00
-- url     : https://prove2.me/theorems/44b1bb10-2eeb-4c96-a475-fc41a8c5e62d
-- title:
--   Free Quotient Rank: free Quot rank span
-- statement:
--   The Free Quotient Rank construction uses the free Quot rank span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FreeQuotPf.lean#L16-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FreeQuotPf.lean#L16-L32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
import Definitions.Def_Lemmata_MiscLemmasJ_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FreeQuotPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Module
variable {R F X : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.freeQuot_rank_span (S : Submodule R X) :
    Module.rank R S = Module.rank F (Submodule.span F (S : Set X)) := by sorry
