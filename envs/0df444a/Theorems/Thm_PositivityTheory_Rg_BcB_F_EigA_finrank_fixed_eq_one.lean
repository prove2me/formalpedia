-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_finrank_fixed_eq_one
-- name    : PositivityTheory.Rg.BcB.F.EigA.finrank_fixed_eq_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:51:55.678538+00:00
-- url     : https://prove2.me/theorems/e33fba46-3c2b-4a13-b7cb-2d0d108cb1f2
-- title:
--   Eig A: finrank fixed eq one
-- statement:
--   The Eig A construction uses the finrank fixed eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/FixedSpaceRankOne/FinrankFixedEqOne.lean#L281-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/FixedSpaceRankOne/FinrankFixedEqOne.lean#L281-L326

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

theorem PositivityTheory.Rg.BcB.F.EigA.finrank_fixed_eq_one {K : Subgroup G} (hK : GelPair K) (ρ : Representation ℂ G V)
    (hirr : ρ.IsIrreducible) (hne : fixed ρ K ≠ ⊥) [FiniteDimensional ℂ (fixed ρ K)] :
    Module.finrank ℂ (fixed ρ K) = 1 := by sorry
