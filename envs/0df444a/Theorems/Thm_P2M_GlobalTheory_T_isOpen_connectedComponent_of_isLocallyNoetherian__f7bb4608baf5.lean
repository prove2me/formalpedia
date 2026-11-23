-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_isOpen_connectedComponent_of_isLocallyNoetherian__f7bb4608baf5
-- name    : P2M_GlobalTheory_T_isOpen_connectedComponent_of_isLocallyNoetherian__f7bb4608baf5
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:18.882006+00:00
-- url     : https://prove2.me/theorems/3e94c6c7-fd36-4345-b08f-ba51c74c371f
-- title:
--   P2 M Global Theory T is Open connected Component of is Locally Noetherian  f7bb4608baf5: P2 M Global Theory T is Open connected Component of is Locally Noetherian  f7bb4608baf5
-- statement:
--   The P2 M Global Theory T is Open connected Component of is Locally Noetherian  f7bb4608baf5 construction uses the P2 M Global Theory T is Open connected Component of is Locally Noetherian  f7bb4608baf5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenConnectedComponentOfIsLocallyNoetherianStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenConnectedComponentOfIsLocallyNoetherianStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenConnectedComponentOfIsLocallyNoetherian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenConnectedComponentOfIsLocallyNoetherianStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_isOpen_connectedComponent_of_isLocallyNoetherian__f7bb4608baf5 : ∀ (X : Scheme.{0}), IsLocallyNoetherian X → ∀ x : X, IsOpen (connectedComponent x) := by sorry

alias «GlobalTheory».«T».«isOpen_connectedComponent_of_isLocallyNoetherian'» := P2M_GlobalTheory_T_isOpen_connectedComponent_of_isLocallyNoetherian__f7bb4608baf5
