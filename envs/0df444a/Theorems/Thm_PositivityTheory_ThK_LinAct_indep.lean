-- Prove2me | Theorems.Thm_PositivityTheory_ThK_LinAct_indep
-- name    : PositivityTheory.ThK.LinAct.indep
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:39:15.166337+00:00
-- url     : https://prove2.me/theorems/e3da0412-62f4-46fa-8042-9479b92c4687
-- title:
--   Lin Act: indep
-- statement:
--   The Lin Act construction uses the indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActAlg.lean#L63-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActAlg.lean#L63-L72

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
omit [Invertible (2 : k)] [Fintype α] [DecidableEq α]

theorem PositivityTheory.ThK.LinAct.indep {Cy Cx : Matrix β ν K} {M : Matrix (ν ⊕ ν) β K} (h2 : M * fromCols Cy Cx = 1) {z z' : Matrix ν α K}
    (h : Cy * z + Cx * z' = 0) : z = 0 ∧ z' = 0 := by sorry
