-- Prove2me | Theorems.Thm_P2M_Formalism_REAL_toM_injective__bc4491a48ce7
-- name    : P2M_Formalism_REAL_toM_injective__bc4491a48ce7
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:31.760089+00:00
-- url     : https://prove2.me/theorems/623a14d1-027d-4cd4-8059-28e7ff3903fe
-- title:
--   P2 M Formalism REAL to M injective  bc4491a48ce7: P2 M Formalism REAL to M injective  bc4491a48ce7
-- statement:
--   The P2 M Formalism REAL to M injective  bc4491a48ce7 construction uses the P2 M Formalism REAL to M injective  bc4491a48ce7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactHaarRightInvariantInst.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactHaarRightInvariantInst.lean#L18-L19

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactHaarRightInvariantInst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory MeasureTheory.Measure
noncomputable section
open Formalism Formalism.REAL

theorem P2M_Formalism_REAL_toM_injective__bc4491a48ce7 {n : ℕ} {ε : Fin n → Bool} {g h : UJ ε} (hgh : toM g = toM h) : g = h := by sorry

alias «Formalism».«REAL».«toM_injective'» := P2M_Formalism_REAL_toM_injective__bc4491a48ce7
