-- Prove2me | Theorems.Thm_P2M_Formalism_DivisionValues_W8_telescope__7f6de1e4cbc8
-- name    : P2M_Formalism_DivisionValues_W8_telescope__7f6de1e4cbc8
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:23.437806+00:00
-- url     : https://prove2.me/theorems/f1ac2cbb-cc39-461a-acff-0f670918a38e
-- title:
--   P2 M Formalism Division Values W8 telescope  7f6de1e4cbc8: P2 M Formalism Division Values W8 telescope  7f6de1e4cbc8
-- statement:
--   The P2 M Formalism Division Values W8 telescope  7f6de1e4cbc8 construction uses the P2 M Formalism Division Values W8 telescope  7f6de1e4cbc8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean#L212-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean#L212-L217

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues.W8

theorem P2M_Formalism_DivisionValues_W8_telescope__7f6de1e4cbc8 {n : ℕ} {c : Fin (n + 1) → ℝ} {c' : Fin n → ℝ} {S : ℝ}
    (h : Formalism.LatticeIndexTer.Interlaced n c c' S) : ∑ i : Fin n, (c' i - c i.succ) ≤ S := by sorry

alias «Formalism».«DivisionValues».«W8».«telescope'» := P2M_Formalism_DivisionValues_W8_telescope__7f6de1e4cbc8
