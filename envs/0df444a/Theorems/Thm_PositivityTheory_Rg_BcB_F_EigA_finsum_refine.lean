-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_finsum_refine
-- name    : PositivityTheory.Rg.BcB.F.EigA.finsum_refine
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:52:22.546266+00:00
-- url     : https://prove2.me/theorems/e5ff720b-d963-5559-b531-22e3b04819dc
-- title:
--   Eig A: finsum refine
-- statement:
--   The Eig A construction uses the finsum refine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/FixedSpaceRankOne/FinrankFixedEqOne.lean#L14-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/FixedSpaceRankOne/FinrankFixedEqOne.lean#L14-L39

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

theorem PositivityTheory.Rg.BcB.F.EigA.finsum_refine {H M : Type} [Group H] [AddCommMonoid M] (A B : Subgroup H) (hAB : A ≤ B)
    [Finite (H ⧸ A)] (F : H → M) (hF : ∀ x, ∀ b ∈ B, F (x * b) = F x) :
    ∑ᶠ q : H ⧸ A, F q.out = (A.relIndex B) • ∑ᶠ q : H ⧸ B, F q.out := by sorry
