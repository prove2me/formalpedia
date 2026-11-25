-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_first_projection
-- name    : ReciprocityTheory.AnForm.M.isPotential_first_projection
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:47:49.13546+00:00
-- url     : https://prove2.me/theorems/50db23fc-2998-45e7-8361-c82761d36fd3
-- title:
--   M: is Potential first projection
-- statement:
--   The M construction uses the is Potential first projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ProdProofB.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ProdProofB.lean#L74-L76

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProdProofA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProdProofB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory Filter Topology FinHolAtlas
open scoped ContDiff
noncomputable section
variable {e e' : ℕ}
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem ReciprocityTheory.AnForm.M.isPotential_first_projection (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (P : LocPot X)
    (hP : IsPotential A P) : IsPotential (prodAtlas A B) (P.pr1 (Y := Y)) := by sorry
