-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_li_of_submodule
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.exists_li_of_submodule
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:28.33149+00:00
-- url     : https://prove2.me/theorems/11ef6a42-f1c9-4bc7-9b78-cb9a50835ebe
-- title:
--   Chart: exists li of submodule
-- statement:
--   The Chart construction uses the exists li of submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankLin.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankLin.lean#L36-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open Module
variable {V k : Type} [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field k] [Algebra V k] [FaithfulSMul V k]

theorem ReciprocityTheory.ChartRestriction.G.Chart.exists_li_of_submodule {ι' : Type} [Fintype ι'] [DecidableEq ι'] (N : Submodule V (ι' → V)) :
    ∃ v : Fin (finrank V N) → ι' → V, LinearIndependent V v ∧ ∀ i, v i ∈ N := by sorry
