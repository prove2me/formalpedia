-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_second_projection
-- name    : ReciprocityTheory.AnForm.M.isPotential_second_projection
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:47:34.373806+00:00
-- url     : https://prove2.me/theorems/aa514768-2d1e-5e59-93e1-5f7567225080
-- title:
--   M: is Potential second projection
-- statement:
--   The M construction uses the is Potential second projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ProdProofB.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ProdProofB.lean#L78-L80

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

theorem ReciprocityTheory.AnForm.M.isPotential_second_projection (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (Q : LocPot Y)
    (hQ : IsPotential B Q) : IsPotential (prodAtlas A B) (Q.pr2 (X := X)) := by sorry
