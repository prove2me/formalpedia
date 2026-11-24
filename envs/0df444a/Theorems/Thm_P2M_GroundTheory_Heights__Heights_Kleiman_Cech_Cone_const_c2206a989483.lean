-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_const_c2206a989483
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_const_c2206a989483
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:55.241846+00:00
-- url     : https://prove2.me/theorems/fbe371dd-c552-465c-86d9-664f5fd274d3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Cone const c2206a989483: P2 M Ground Theory Heights  Heights Kleiman Cech Cone const c2206a989483
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Cone const c2206a989483 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Cone const c2206a989483 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechCone.lean#L92-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechCone.lean#L92-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
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
open GroundTheory.Heights₂.Heights.Kleiman.Cech GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_const_c2206a989483 {z : Cech.Cochain (fun _ : StdCell N => V) 0}
    (hz : Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) 0 z = 0)
    (I K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0) : z I = z K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«Cone».«const» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_const_c2206a989483
