-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_card_le_finrank_of_li
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.card_le_finrank_of_li
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:16.312291+00:00
-- url     : https://prove2.me/theorems/a370d713-3f9c-5e86-b9ca-69989f10d676
-- title:
--   Chart: card le finrank of li
-- statement:
--   The Chart construction uses the card le finrank of li property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankLin.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankLin.lean#L28-L34

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.card_le_finrank_of_li {ι' ι : Type} [Fintype ι'] [Fintype ι] (v : ι → ι' → V) (hv : LinearIndependent V v)
    (W : Submodule k (ι' → k)) (hW : ∀ i, (algebraMap V k ∘ v i) ∈ W) : Fintype.card ι ≤ finrank k W := by sorry
