-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LatL_norm_sub_le_max_ultra__b241ffa55670
-- name    : P2M_GlobalTheory_LatL_norm_sub_le_max_ultra__b241ffa55670
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:07:09.460958+00:00
-- url     : https://prove2.me/theorems/ece1ee2c-d613-4158-ac8e-14e606d07d55
-- title:
--   P2 M Global Theory Lat L norm sub le max ultra  b241ffa55670: P2 M Global Theory Lat L norm sub le max ultra  b241ffa55670
-- statement:
--   The P2 M Global Theory Lat L norm sub le max ultra  b241ffa55670 construction uses the P2 M Global Theory Lat L norm sub le max ultra  b241ffa55670 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormSubLeMaxUltra.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormSubLeMaxUltra.lean#L6-L9

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormSubLeMaxUltra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.LatL

theorem P2M_GlobalTheory_LatL_norm_sub_le_max_ultra__b241ffa55670 {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) :
    ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by sorry

alias «GlobalTheory».«LatL».«norm_sub_le_max_ultra'» := P2M_GlobalTheory_LatL_norm_sub_le_max_ultra__b241ffa55670
