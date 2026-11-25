-- Prove2me | Theorems.Thm_P2M_Formalism_G0_TopsWeightFunctionBounds_Phi_init__f265b99736a1
-- name    : P2M_Formalism_G0_TopsWeightFunctionBounds_Phi_init__f265b99736a1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:56:35.981961+00:00
-- url     : https://prove2.me/theorems/fa3aa265-4da2-4ffc-bcc7-36c112375500
-- title:
--   P2 M Formalism G0 Tops Weight Function Bounds Phi init  f265b99736a1: P2 M Formalism G0 Tops Weight Function Bounds Phi init  f265b99736a1
-- statement:
--   The P2 M Formalism G0 Tops Weight Function Bounds Phi init  f265b99736a1 construction uses the P2 M Formalism G0 Tops Weight Function Bounds Phi init  f265b99736a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L807-L813
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L807-L813

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds

theorem P2M_Formalism_G0_TopsWeightFunctionBounds_Phi_init__f265b99736a1 {R L₂ : ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1)
    (hR : 1 ≤ R) (K : ℕ) (ev : Bool) :
    Phi R L₂ δ (init K ev) ≤ (1 - aF L₂ δ ^ R) ^ K := by sorry

alias «Formalism».«G0».«TopsWeightFunctionBounds».«Phi_init'» := P2M_Formalism_G0_TopsWeightFunctionBounds_Phi_init__f265b99736a1
