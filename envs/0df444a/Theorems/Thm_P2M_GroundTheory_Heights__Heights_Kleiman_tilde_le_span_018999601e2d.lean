-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_tilde_le_span_018999601e2d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_tilde_le_span_018999601e2d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:03.813808+00:00
-- url     : https://prove2.me/theorems/d6a5faee-29cc-4770-9754-f613b71c7bcd
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman tilde le span 018999601e2d: P2 M Ground Theory Heights  Heights Kleiman tilde le span 018999601e2d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman tilde le span 018999601e2d construction uses the P2 M Ground Theory Heights  Heights Kleiman tilde le span 018999601e2d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailLoc.lean#L118-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailLoc.lean#L118-L140

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (M : FinGradedSub (S := S) (x := x) Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_tilde_le_span_018999601e2d (c : ℤ) (I : Chart x) :
    (M.tilde c I : Set Ω) ⊆ Submodule.span S (tildeGens M c I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«tilde_le_span» := P2M_GroundTheory_Heights__Heights_Kleiman_tilde_le_span_018999601e2d
