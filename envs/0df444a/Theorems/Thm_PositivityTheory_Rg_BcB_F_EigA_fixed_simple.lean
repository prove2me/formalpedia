-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_fixed_simple
-- name    : PositivityTheory.Rg.BcB.F.EigA.fixed_simple
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:52:15.761193+00:00
-- url     : https://prove2.me/theorems/5347763c-9bd6-5c7b-b4d6-ea6153f513a2
-- title:
--   Eig A: fixed simple
-- statement:
--   The Eig A construction uses the fixed simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/FixedSpaceRankOne/FinrankFixedEqOne.lean#L215-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/FixedSpaceRankOne/FinrankFixedEqOne.lean#L215-L279

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

theorem PositivityTheory.Rg.BcB.F.EigA.fixed_simple {K : Subgroup G} (hK : GelPair K) (ρ : Representation ℂ G V) (hirr : ρ.IsIrreducible)
    (W : Submodule ℂ (fixed ρ K)) (hW : W ≠ ⊥)
    (hst : ∀ g : G, ∀ w : fixed ρ K, w ∈ W → ∀ y : fixed ρ K, (y : V) = hop ρ K g w → y ∈ W) : W = ⊤ := by sorry
