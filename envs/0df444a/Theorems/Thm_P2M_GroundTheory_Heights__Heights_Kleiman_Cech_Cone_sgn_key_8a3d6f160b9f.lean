-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_key_8a3d6f160b9f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_key_8a3d6f160b9f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:10.422796+00:00
-- url     : https://prove2.me/theorems/85231d7a-b64f-48c0-9ad2-2d3bb148eff3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Cone sgn key 8a3d6f160b9f: P2 M Ground Theory Heights  Heights Kleiman Cech Cone sgn key 8a3d6f160b9f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Cone sgn key 8a3d6f160b9f construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Cone sgn key 8a3d6f160b9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechCone.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechCone.lean#L30-L44

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
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_key_8a3d6f160b9f {K : Finset (Fin n)} {i₀ j : Fin n} (hi₀ : i₀ ∉ K) (hj : j ∈ K) :
    Cech.sgn K j * Cech.sgn (insert i₀ (K.erase j)) i₀ =
      -(Cech.sgn (insert i₀ K) i₀ * Cech.sgn (insert i₀ K) j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«Cone».«sgn_key» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_key_8a3d6f160b9f
