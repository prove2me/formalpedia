-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Restriction_proof_d94c101ca059
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Restriction_proof_d94c101ca059
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:05:43.821431+00:00
-- url     : https://prove2.me/theorems/56ed68c3-2cc7-51d3-abfd-ff9233ecb171
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restriction proof d94c101ca059: P2 M Ground Theory Heights  Heights Kleiman Restriction proof d94c101ca059
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restriction proof d94c101ca059 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restriction proof d94c101ca059 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestriction.lean#L224-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestriction.lean#L224-L230

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Restriction_proof_d94c101ca059 : Restriction.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Restriction».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_Restriction_proof_d94c101ca059
