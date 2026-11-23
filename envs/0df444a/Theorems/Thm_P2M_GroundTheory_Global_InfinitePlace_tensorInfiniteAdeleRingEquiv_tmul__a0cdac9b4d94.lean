-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_InfinitePlace_tensorInfiniteAdeleRingEquiv_tmul__a0cdac9b4d94
-- name    : P2M_GroundTheory_Global_InfinitePlace_tensorInfiniteAdeleRingEquiv_tmul__a0cdac9b4d94
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:23.02407+00:00
-- url     : https://prove2.me/theorems/b004b04c-909f-49c1-b09d-b91bf35a246c
-- title:
--   P2 M Ground Theory Global Infinite Place tensor Infinite Adele Ring Equiv tmul  a0cdac9b4d94: P2 M Ground Theory Global Infinite Place tensor Infinite Adele Ring Equiv tmul  a0cdac9b4d94
-- statement:
--   The P2 M Ground Theory Global Infinite Place tensor Infinite Adele Ring Equiv tmul  a0cdac9b4d94 construction uses the P2 M Ground Theory Global Infinite Place tensor Infinite Adele Ring Equiv tmul  a0cdac9b4d94 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/InfiniteAdele.lean#L89-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/InfiniteAdele.lean#L89-L94

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct
open GroundTheory.Global.InfinitePlace
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [NumberField K] [NumberField L]

theorem P2M_GroundTheory_Global_InfinitePlace_tensorInfiniteAdeleRingEquiv_tmul__a0cdac9b4d94 (l : L) (x : InfiniteAdeleRing K) :
    tensorInfiniteAdeleRingEquiv (l ⊗ₜ x) =
      algebraMap L (InfiniteAdeleRing L) l * infiniteAdeleRingMap x := by sorry

alias «GroundTheory».«Global».«InfinitePlace».«tensorInfiniteAdeleRingEquiv_tmul'» := P2M_GroundTheory_Global_InfinitePlace_tensorInfiniteAdeleRingEquiv_tmul__a0cdac9b4d94
