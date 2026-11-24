-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_finrank_eq_7a942c89c61a
-- name    : P2M_GroundTheory_Heights__Heights_HermitianExtension_finrank_eq_7a942c89c61a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:09.986187+00:00
-- url     : https://prove2.me/theorems/8ebca677-be70-4004-8b59-fef71638bcfb
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Extension finrank eq 7a942c89c61a: P2 M Ground Theory Heights  Heights Hermitian Extension finrank eq 7a942c89c61a
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Extension finrank eq 7a942c89c61a construction uses the P2 M Ground Theory Heights  Heights Hermitian Extension finrank eq 7a942c89c61a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L111-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L111-L123

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
include X

theorem P2M_GroundTheory_Heights__Heights_HermitianExtension_finrank_eq_7a942c89c61a : Module.finrank (𝓞 K) E.carrier =
    Module.finrank (𝓞 K) E'.carrier + Module.finrank (𝓞 K) E''.carrier := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianExtension».«finrank_eq» := P2M_GroundTheory_Heights__Heights_HermitianExtension_finrank_eq_7a942c89c61a
