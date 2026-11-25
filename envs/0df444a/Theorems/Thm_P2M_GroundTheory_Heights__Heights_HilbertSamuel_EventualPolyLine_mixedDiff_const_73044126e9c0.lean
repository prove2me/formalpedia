-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_mixedDiff_const_73044126e9c0
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_mixedDiff_const_73044126e9c0
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:50.121017+00:00
-- url     : https://prove2.me/theorems/4cbeff67-e4e8-4252-aebb-b61d24ed16e5
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line mixed Diff const 73044126e9c0: P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line mixed Diff const 73044126e9c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line mixed Diff const 73044126e9c0 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line mixed Diff const 73044126e9c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolyLine.lean#L86-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolyLine.lean#L86-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolyLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolyLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial GroundTheory.Heights₂.Heights.NumbersDVR fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
variable {K : Type}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_mixedDiff_const_73044126e9c0 (D : ℕ) (a : K → ℤ) (f : (K → ℤ) → ℤ) :
    mixedDiff (fun _ : Fin D => a) f = (List.replicate D a).foldr diffStep f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«EventualPolyLine».«mixedDiff_const» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_mixedDiff_const_73044126e9c0
