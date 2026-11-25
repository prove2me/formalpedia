-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_restrictTo_eq_6615ffe29c1d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_restrictTo_eq_6615ffe29c1d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:26:59.900905+00:00
-- url     : https://prove2.me/theorems/81e16b4b-083a-41ca-ac43-941b6cef92c5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech DSq restrict To eq 6615ffe29c1d: P2 M Ground Theory Heights  Heights Kleiman Cech DSq restrict To eq 6615ffe29c1d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech DSq restrict To eq 6615ffe29c1d construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech DSq restrict To eq 6615ffe29c1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDSq.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDSq.lean#L46-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
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
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.CechDSq
variable {n : ℕ}
variable {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_restrictTo_eq_6615ffe29c1d {i : ℕ} (s : Cech.Cochain G i) (K : Cell U) (L : Cech.Idx U i)
    (h : L.1.1 ⊆ K.1) : restrictTo (ρ := ρ) s K L.1.1 = ρ L.1 K h (s L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDSq».«restrictTo_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_restrictTo_eq_6615ffe29c1d
