-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_lexEmb_injective_2e035ab13206
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_lexEmb_injective_2e035ab13206
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:44.558206+00:00
-- url     : https://prove2.me/theorems/8dbef08d-1157-404d-ad88-8b27d175deb6
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration lex Emb injective 2e035ab13206: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration lex Emb injective 2e035ab13206
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration lex Emb injective 2e035ab13206 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration lex Emb injective 2e035ab13206 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L36-L40

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_lexEmb_injective_2e035ab13206 : Function.Injective (lexEmb K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«lexEmb_injective» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_lexEmb_injective_2e035ab13206
