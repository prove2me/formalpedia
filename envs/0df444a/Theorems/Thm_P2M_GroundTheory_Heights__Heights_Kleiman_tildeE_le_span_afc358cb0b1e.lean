-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_tildeE_le_span_afc358cb0b1e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_tildeE_le_span_afc358cb0b1e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:20.631606+00:00
-- url     : https://prove2.me/theorems/0e783ba2-2821-40ac-91a6-2270aeac3c6c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman tilde E le span afc358cb0b1e: P2 M Ground Theory Heights  Heights Kleiman tilde E le span afc358cb0b1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman tilde E le span afc358cb0b1e construction uses the P2 M Ground Theory Heights  Heights Kleiman tilde E le span afc358cb0b1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishLoc.lean#L105-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishLoc.lean#L105-L131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
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
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_tildeE_le_span_afc358cb0b1e (c : ℤ) (I : Chart x) :
    (M.tilde c I : Set E) ⊆ Submodule.span S (tildeGensE M c I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«tildeE_le_span» := P2M_GroundTheory_Heights__Heights_Kleiman_tildeE_le_span_afc358cb0b1e
