-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_hop_comm
-- name    : PositivityTheory.Rg.BcB.F.EigA.hop_comm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:37.199176+00:00
-- url     : https://prove2.me/theorems/77725677-2296-48af-93a8-6c5df35d560d
-- title:
--   Eig A: hop comm
-- statement:
--   The Eig A construction uses the hop comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/FixedSpaceRankOne/FinrankFixedEqOne.lean#L199-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/FixedSpaceRankOne/FinrankFixedEqOne.lean#L199-L209

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.EigA
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem PositivityTheory.Rg.BcB.F.EigA.hop_comm {K : Subgroup G} (hK : GelPair K) (ρ : Representation ℂ G V) (g h : G) {v : V}
    (hv : v ∈ fixed ρ K) : hop ρ K g (hop ρ K h v) = hop ρ K h (hop ρ K g v) := by sorry
