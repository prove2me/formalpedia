-- Prove2me | Theorems.Thm_PI_UnimodIdxWork_mem_conj_map
-- name    : PI.UnimodIdxWork.mem_conj_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:30:58.556549+00:00
-- url     : https://prove2.me/theorems/95aa6671-4378-4a46-b30d-2f8c05b82503
-- title:
--   Unimod Idx Work: mem conj map
-- statement:
--   The Unimod Idx Work construction uses the mem conj map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularIndex/PairwiseDisjointCosets.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularIndex/PairwiseDisjointCosets.lean#L58-L65

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

theorem PI.UnimodIdxWork.mem_conj_map (K : Subgroup G) (g y : G) :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by sorry
