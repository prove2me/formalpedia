-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_pair_39898383e827
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_pair_39898383e827
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:32.581982+00:00
-- url     : https://prove2.me/theorems/2119624b-ca74-4e8d-a521-4d854238a2bc
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Cone on Set pair 39898383e827: P2 M Ground Theory Heights  Heights Kleiman Cech Cone on Set pair 39898383e827
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Cone on Set pair 39898383e827 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Cone on Set pair 39898383e827 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechCone.lean#L73-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechCone.lean#L73-L90

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_pair_39898383e827 {z : Cech.Cochain (fun _ : StdCell N => V) 0}
    (hz : Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) 0 z = 0)
    {a b : Fin (N + 1)} (hab : a < b) : onSet z {a} = onSet z {b} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«Cone».«onSet_pair» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_pair_39898383e827
