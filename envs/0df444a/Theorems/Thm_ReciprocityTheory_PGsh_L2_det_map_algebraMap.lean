-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_det_map_algebraMap
-- name    : ReciprocityTheory.PGsh.L2.det_map_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:56.950009+00:00
-- url     : https://prove2.me/theorems/8ae98fc1-e3f6-4441-b221-6d9e512aa752
-- title:
--   L2: det map algebra Map
-- statement:
--   The L2 construction uses the det map algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsUnitDetOfSpanEq.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsUnitDetOfSpanEq.lean#L11-L14

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}

theorem ReciprocityTheory.PGsh.L2.det_map_algebraMap {X : Type} [Fintype X] [DecidableEq X] (M : Matrix X X R) :
    (M.map (algebraMap R C)).det = algebraMap R C M.det := by sorry
