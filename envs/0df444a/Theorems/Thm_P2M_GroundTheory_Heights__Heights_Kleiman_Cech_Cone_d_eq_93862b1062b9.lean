-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_d_eq_93862b1062b9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_d_eq_93862b1062b9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:24.917294+00:00
-- url     : https://prove2.me/theorems/0d60b2c4-ed8d-4417-8880-aea6273c17db
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Cone d eq 93862b1062b9: P2 M Ground Theory Heights  Heights Kleiman Cech Cone d eq 93862b1062b9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Cone d eq 93862b1062b9 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Cone d eq 93862b1062b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechCone.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechCone.lean#L60-L67

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_d_eq_93862b1062b9 {i : ℕ} (s : Cech.Cochain (fun _ : StdCell N => V) i)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) (i + 1)) :
    Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) i s K =
      ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • onSet s (K.1.1.erase j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«Cone».«d_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_d_eq_93862b1062b9
