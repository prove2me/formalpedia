-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_idx_b45b833a5674
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_idx_b45b833a5674
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:42.318438+00:00
-- url     : https://prove2.me/theorems/7faa5f12-e717-4896-adf3-137817322f92
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Cone on Set idx b45b833a5674: P2 M Ground Theory Heights  Heights Kleiman Cech Cone on Set idx b45b833a5674
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Cone on Set idx b45b833a5674 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Cone on Set idx b45b833a5674 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechCone.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechCone.lean#L55-L58

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_idx_b45b833a5674 {i : ℕ} (s : Cech.Cochain (fun _ : StdCell N => V) i)
    (I : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) : onSet s I.1.1 = s I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«Cone».«onSet_idx» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_idx_b45b833a5674
