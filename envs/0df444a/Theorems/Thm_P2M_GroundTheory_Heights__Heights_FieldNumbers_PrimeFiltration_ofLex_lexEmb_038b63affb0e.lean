-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_ofLex_lexEmb_038b63affb0e
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_ofLex_lexEmb_038b63affb0e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:01.804685+00:00
-- url     : https://prove2.me/theorems/ec9b3d16-0256-4105-8599-c36d1a4f7886
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration of Lex lex Emb 038b63affb0e: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration of Lex lex Emb 038b63affb0e
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration of Lex lex Emb 038b63affb0e construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration of Lex lex Emb 038b63affb0e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L32-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance 2000] lexDecEq
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_ofLex_lexEmb_038b63affb0e (b : K → ℕ) (i : Fin (Fintype.card K)) :
    ofLex (lexEmb K b) i = b ((blockIdx K).symm i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«ofLex_lexEmb» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_ofLex_lexEmb_038b63affb0e
