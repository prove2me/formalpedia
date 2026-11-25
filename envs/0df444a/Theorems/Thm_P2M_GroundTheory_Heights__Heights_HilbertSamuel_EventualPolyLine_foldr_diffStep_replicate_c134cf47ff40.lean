-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_foldr_diffStep_replicate_c134cf47ff40
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_foldr_diffStep_replicate_c134cf47ff40
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:49.870375+00:00
-- url     : https://prove2.me/theorems/dbde165e-dd9e-5131-80e2-94903a046be2
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line foldr diff Step replicate c134cf47ff40: P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line foldr diff Step repl
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line foldr diff Step replicate c134cf47ff40 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line foldr diff Step replicate c134cf47ff40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolyLine.lean#L90-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolyLine.lean#L90-L101

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_foldr_diffStep_replicate_c134cf47ff40 (a : K → ℤ) (f : (K → ℤ) → ℤ) (n : ℕ) (x : K → ℤ) :
    (List.replicate n a).foldr diffStep f x = (fwdDiff a)^[n] f (x - n • a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«EventualPolyLine».«foldr_diffStep_replicate» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_foldr_diffStep_replicate_c134cf47ff40
