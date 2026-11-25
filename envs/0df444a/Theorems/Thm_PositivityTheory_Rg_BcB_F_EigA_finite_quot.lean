-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_finite_quot
-- name    : PositivityTheory.Rg.BcB.F.EigA.finite_quot
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:52:52.154933+00:00
-- url     : https://prove2.me/theorems/f53369df-ee9c-53fc-bf00-4edc67c8a163
-- title:
--   Eig A: finite quot
-- statement:
--   The Eig A construction uses the finite quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/FixedSpaceRankOne/FinrankFixedEqOne.lean#L211-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/FixedSpaceRankOne/FinrankFixedEqOne.lean#L211-L213

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

theorem PositivityTheory.Rg.BcB.F.EigA.finite_quot {K : Subgroup G} (hK : GelPair K) (g : G) : Finite (K ⧸ stabK K g) := by sorry
