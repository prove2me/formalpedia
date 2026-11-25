-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_trace_mul_of_finrank_one
-- name    : PositivityTheory.Rg.BcB.F.EigA.trace_mul_of_finrank_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:51:28.51692+00:00
-- url     : https://prove2.me/theorems/51806ce1-f905-465c-bcbf-dc9868844c8b
-- title:
--   Eig A: trace mul of finrank one
-- statement:
--   The Eig A construction uses the trace mul of finrank one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/FixedSpaceRankOne/TraceMulOfFinrankOne.lean#L93-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/FixedSpaceRankOne/TraceMulOfFinrankOne.lean#L93-L102

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_TraceMulOfFinrankOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Pointwise
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.EigA
variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.BcB.F.EigA.trace_mul_of_finrank_one (h : Module.finrank ℂ M = 1) (f g : Module.End ℂ M) :
    LinearMap.trace ℂ M (f * g) = LinearMap.trace ℂ M f * LinearMap.trace ℂ M g := by sorry
