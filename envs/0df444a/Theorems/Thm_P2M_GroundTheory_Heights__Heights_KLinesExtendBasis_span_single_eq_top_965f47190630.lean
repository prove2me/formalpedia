-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesExtendBasis_span_single_eq_top_965f47190630
-- name    : P2M_GroundTheory_Heights__Heights_KLinesExtendBasis_span_single_eq_top_965f47190630
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:20.917233+00:00
-- url     : https://prove2.me/theorems/cf06e9a8-2040-4cf3-87af-af2b621e1141
-- title:
--   P2 M Ground Theory Heights  Heights KLines Extend Basis span single eq top 965f47190630: P2 M Ground Theory Heights  Heights KLines Extend Basis span single eq top 965f47190630
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Extend Basis span single eq top 965f47190630 construction uses the P2 M Ground Theory Heights  Heights KLines Extend Basis span single eq top 965f47190630 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesExtendBasis.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesExtendBasis.lean#L9-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesExtendBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KLinesExtendBasis

theorem P2M_GroundTheory_Heights__Heights_KLinesExtendBasis_span_single_eq_top_965f47190630 (K : Type) [Field K] (n : ℕ) :
    Submodule.span K (Set.range fun x : Fin n => (Pi.single x 1 : Fin n → K)) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesExtendBasis».«span_single_eq_top» := P2M_GroundTheory_Heights__Heights_KLinesExtendBasis_span_single_eq_top_965f47190630
