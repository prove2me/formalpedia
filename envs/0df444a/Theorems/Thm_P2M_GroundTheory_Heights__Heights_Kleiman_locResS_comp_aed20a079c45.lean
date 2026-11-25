-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locResS_comp_aed20a079c45
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locResS_comp_aed20a079c45
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:36:22.874798+00:00
-- url     : https://prove2.me/theorems/acea149c-b382-573d-9e00-2c1e13878d5a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Res S comp aed20a079c45: P2 M Ground Theory Heights  Heights Kleiman loc Res S comp aed20a079c45
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Res S comp aed20a079c45 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Res S comp aed20a079c45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsCechDSq.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsCechDSq.lean#L26-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
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
universe u v
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locResS_comp_aed20a079c45 (I J K : StdCell N) (hIJ : I.1 ⊆ J.1) (hJK : J.1 ⊆ K.1) :
    (locResS (S := S) (M := M) J K hJK).comp (locResS I J hIJ) = locResS I K (hIJ.trans hJK) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locResS_comp» := P2M_GroundTheory_Heights__Heights_Kleiman_locResS_comp_aed20a079c45
