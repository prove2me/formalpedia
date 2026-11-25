-- Prove2me | Theorems.Thm_PositivityTheory_ThK_LinAct_hTens_transpose
-- name    : PositivityTheory.ThK.LinAct.hTens_transpose
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:04:26.738522+00:00
-- url     : https://prove2.me/theorems/ef6e957a-038f-476d-9129-70b4867c800b
-- title:
--   Lin Act: h Tens transpose
-- statement:
--   The Lin Act construction uses the h Tens transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActAlg.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActAlg.lean#L16-L24

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LagrangianStabilizerCharacterTrivial
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_LinearActAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.LinAct
set_option linter.unusedSectionVars false
variable {k : Type} [Field k] [Invertible (2 : k)] {K : Type} [CommRing K] [Algebra k K] {c : K →ₐ[k] K}
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
omit [Invertible (2 : k)] [DecidableEq α] [DecidableEq β]

theorem PositivityTheory.ThK.LinAct.hTens_transpose (JA : Matrix α α K) (JB : Matrix β β K) (x y : Matrix β α K) :
    hTens c JB JA x y = hTens c JA JB xᵀ yᵀ := by sorry
