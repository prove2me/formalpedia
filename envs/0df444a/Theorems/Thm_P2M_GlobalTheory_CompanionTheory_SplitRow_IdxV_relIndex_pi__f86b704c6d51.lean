-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SplitRow_IdxV_relIndex_pi__f86b704c6d51
-- name    : P2M_GlobalTheory_CompanionTheory_SplitRow_IdxV_relIndex_pi__f86b704c6d51
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:19.510687+00:00
-- url     : https://prove2.me/theorems/fe779c5e-bdb5-4342-8ce2-a4b6160ed602
-- title:
--   P2 M Global Theory Companion Theory Split Row Idx V rel Index pi  f86b704c6d51: P2 M Global Theory Companion Theory Split Row Idx V rel Index pi  f86b704c6d51
-- statement:
--   The P2 M Global Theory Companion Theory Split Row Idx V rel Index pi  f86b704c6d51 construction uses the P2 M Global Theory Companion Theory Split Row Idx V rel Index pi  f86b704c6d51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/IsArtinianRingKummerAdjoinRootQuotientRoot.lean#L10-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/IsArtinianRingKummerAdjoinRootQuotientRoot.lean#L10-L27

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_HasElemDiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.SplitRow GlobalTheory.CompanionTheory.FinHeis GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitRow GlobalTheory.CompanionTheory.SplitRow.IdxV

theorem P2M_GlobalTheory_CompanionTheory_SplitRow_IdxV_relIndex_pi__f86b704c6d51 {ι G : Type} [Fintype ι] [AddCommGroup G] (H K : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ H).relIndex (AddSubgroup.pi Set.univ K) = ∏ i, (H i).relIndex (K i) := by sorry

alias «GlobalTheory».«CompanionTheory».«SplitRow».«IdxV».«relIndex_pi'» := P2M_GlobalTheory_CompanionTheory_SplitRow_IdxV_relIndex_pi__f86b704c6d51
