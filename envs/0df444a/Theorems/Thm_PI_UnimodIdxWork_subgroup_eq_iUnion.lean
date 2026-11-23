-- Prove2me | Theorems.Thm_PI_UnimodIdxWork_subgroup_eq_iUnion
-- name    : PI.UnimodIdxWork.subgroup_eq_iUnion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:46.884916+00:00
-- url     : https://prove2.me/theorems/65751324-dd19-4555-b4d2-3440d6078520
-- title:
--   Unimod Idx Work: subgroup eq i Union
-- statement:
--   The Unimod Idx Work construction uses the subgroup eq i Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularIndex/PairwiseDisjointCosets.lean#L14-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularIndex/PairwiseDisjointCosets.lean#L14-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnimodIdx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularIndex_PairwiseDisjointCosets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Pointwise Set Function
noncomputable section
open PI PI.UnimodIdxWork
variable {G : Type} [Group G]

theorem PI.UnimodIdxWork.subgroup_eq_iUnion (A H : Subgroup G) :
    (H : Set G) = ⋃ q : H ⧸ A.subgroupOf H, ((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G) := by sorry
