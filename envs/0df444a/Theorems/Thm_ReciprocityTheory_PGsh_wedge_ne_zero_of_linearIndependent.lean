-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_wedge_ne_zero_of_linearIndependent
-- name    : ReciprocityTheory.PGsh.wedge_ne_zero_of_linearIndependent
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:38:15.337843+00:00
-- url     : https://prove2.me/theorems/f84b1a1b-0339-40d8-a672-78a80be8dbcb
-- title:
--   PGsh: wedge ne zero of linear Independent
-- statement:
--   The PGsh construction uses the wedge ne zero of linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/WedgeNeZeroOfLinearIndependent.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/WedgeNeZeroOfLinearIndependent.lean#L55-L61

import Definitions.Def_ReciprocityTheory_DualLattices_SmallLevelClassSet
import Definitions.Def_ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open ReciprocityTheory ReciprocityTheory.PGsh
attribute [local instance] extModR
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem ReciprocityTheory.PGsh.wedge_ne_zero_of_linearIndependent {k : ℕ} {b : Fin k → V} (hb : LinearIndependent K b) :
    ExteriorAlgebra.ιMulti K k b ≠ 0 := by sorry
