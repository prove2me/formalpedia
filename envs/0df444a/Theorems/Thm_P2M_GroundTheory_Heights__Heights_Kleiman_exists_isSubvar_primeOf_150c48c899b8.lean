-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_isSubvar_primeOf_150c48c899b8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_isSubvar_primeOf_150c48c899b8
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:28.889353+00:00
-- url     : https://prove2.me/theorems/2f93a2be-d381-4aa5-89d9-820da913b00d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists is Subvar prime Of 150c48c899b8: P2 M Ground Theory Heights  Heights Kleiman exists is Subvar prime Of 150c48c899b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists is Subvar prime Of 150c48c899b8 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists is Subvar prime Of 150c48c899b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L110-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L110-L157

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_isSubvar_primeOf_150c48c899b8 (hx : x ≠ 0) : ∃ d : ℕ, IsSubvar x (primeOf (S := k) x) d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_isSubvar_primeOf» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_isSubvar_primeOf_150c48c899b8
