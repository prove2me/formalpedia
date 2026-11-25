-- Prove2me | Theorems.Thm_PositivityTheory_ThKH_Locrep_linearIndependent_of_notMem
-- name    : PositivityTheory.ThKH.Locrep.linearIndependent_of_notMem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:05:12.589919+00:00
-- url     : https://prove2.me/theorems/5843c266-3cec-433f-86dd-1bbb3319ba9f
-- title:
--   Locrep: linear Independent of not Mem
-- statement:
--   The Locrep construction uses the linear Independent of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LinearIndependentOfNotMem.lean#L14-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LinearIndependentOfNotMem.lean#L14-L35

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsSideBis
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_LinearIndependentOfNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Locrep
open Filter Topology

theorem PositivityTheory.ThKH.Locrep.linearIndependent_of_notMem {V : Type} [AddCommGroup V] [Module ℂ V] (u : ℕ → V) (T : ℕ → Set V)
    (h1 : ∀ m n, m < n → u m ∈ T n) (h2 : ∀ n, u n ∉ Submodule.span ℂ (T n)) : LinearIndependent ℂ u := by sorry
