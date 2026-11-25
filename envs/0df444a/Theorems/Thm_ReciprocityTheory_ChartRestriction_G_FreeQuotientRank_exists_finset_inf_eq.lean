-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_exists_finset_inf_eq
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.exists_finset_inf_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:03.820373+00:00
-- url     : https://prove2.me/theorems/7fc7d57a-3092-475a-b731-247a63378f3a
-- title:
--   Free Quotient Rank: exists finset inf eq
-- statement:
--   The Free Quotient Rank construction uses the exists finset inf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/KerCorePf.lean#L10-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/KerCorePf.lean#L10-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_KerCoreSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_KerCorePf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
open TensorProduct

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.exists_finset_inf_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Set (Submodule K V)) : ∃ t : Finset (Submodule K V), (t : Set _) ⊆ S ∧ ∀ N ∈ S, t.inf id ≤ N := by sorry
