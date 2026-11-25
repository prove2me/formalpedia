-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_det_blockDiagonal__aa8633837095
-- name    : P2M_GroundTheory_Global_SemiLocal_det_blockDiagonal__aa8633837095
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:37:53.87779+00:00
-- url     : https://prove2.me/theorems/34af72b5-0d92-4f54-ab47-ec0ad7bb3ed7
-- title:
--   P2 M Ground Theory Global Semi Local det block Diagonal  aa8633837095: P2 M Ground Theory Global Semi Local det block Diagonal  aa8633837095
-- statement:
--   The P2 M Ground Theory Global Semi Local det block Diagonal  aa8633837095 construction uses the P2 M Ground Theory Global Semi Local det block Diagonal  aa8633837095 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/NormTrace.lean#L12-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/NormTrace.lean#L12-L25

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Matrix
noncomputable section
open GroundTheory.Global.SemiLocal

theorem P2M_GroundTheory_Global_SemiLocal_det_blockDiagonal__aa8633837095 {α : Type*} [Fintype α] [DecidableEq α] {m : α → Type*}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {R : Type*} [CommRing R]
    (d : ∀ i, Matrix (m i) (m i) R) : (blockDiagonal' d).det = ∏ k, (d k).det := by sorry

alias «GroundTheory».«Global».«SemiLocal».«det_blockDiagonal'» := P2M_GroundTheory_Global_SemiLocal_det_blockDiagonal__aa8633837095
