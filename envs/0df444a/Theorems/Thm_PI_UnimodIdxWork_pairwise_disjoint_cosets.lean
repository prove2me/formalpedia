-- Prove2me | Theorems.Thm_PI_UnimodIdxWork_pairwise_disjoint_cosets
-- name    : PI.UnimodIdxWork.pairwise_disjoint_cosets
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:48.000804+00:00
-- url     : https://prove2.me/theorems/3d094e3e-0d5c-420f-a80d-71026e5117e5
-- title:
--   Unimod Idx Work: pairwise disjoint cosets
-- statement:
--   The Unimod Idx Work construction uses the pairwise disjoint cosets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularIndex/PairwiseDisjointCosets.lean#L37-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularIndex/PairwiseDisjointCosets.lean#L37-L56

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

theorem PI.UnimodIdxWork.pairwise_disjoint_cosets (A H : Subgroup G) :
    Pairwise (Disjoint on fun q : H ⧸ A.subgroupOf H =>
      ((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G)) := by sorry
