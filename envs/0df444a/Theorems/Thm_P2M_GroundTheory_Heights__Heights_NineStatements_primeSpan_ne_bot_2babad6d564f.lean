-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_primeSpan_ne_bot_2babad6d564f
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_primeSpan_ne_bot_2babad6d564f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:44.730376+00:00
-- url     : https://prove2.me/theorems/4ba00ab4-c3d4-4c33-83e3-9ddd830d8305
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements prime Span ne bot 2babad6d564f: P2 M Ground Theory Heights  Heights Nine Statements prime Span ne bot 2babad6d564f
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements prime Span ne bot 2babad6d564f construction uses the P2 M Ground Theory Heights  Heights Nine Statements prime Span ne bot 2babad6d564f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigenInputs.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigenInputs.lean#L55-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem P2M_GroundTheory_Heights__Heights_NineStatements_primeSpan_ne_bot_2babad6d564f {L : Type} [Field L] [NumberField L] {q : ℕ} (hq : q.Prime) :
    (Ideal.span {(q : 𝓞 L)} : Ideal (𝓞 L)) ≠ ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«primeSpan_ne_bot» := P2M_GroundTheory_Heights__Heights_NineStatements_primeSpan_ne_bot_2babad6d564f
