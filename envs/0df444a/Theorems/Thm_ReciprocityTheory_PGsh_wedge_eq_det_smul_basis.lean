-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_wedge_eq_det_smul_basis
-- name    : ReciprocityTheory.PGsh.wedge_eq_det_smul_basis
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:35.411813+00:00
-- url     : https://prove2.me/theorems/9399442e-3055-5ce1-ac2f-e6ec51e18fbe
-- title:
--   PGsh: wedge eq det smul basis
-- statement:
--   The PGsh construction uses the wedge eq det smul basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/WedgeNeZeroOfLinearIndependent.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/WedgeNeZeroOfLinearIndependent.lean#L15-L28

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

theorem ReciprocityTheory.PGsh.wedge_eq_det_smul_basis {k : ℕ} {W : Submodule K V} (bW : Basis (Fin k) K W) (w : Fin k → W) :
    ExteriorAlgebra.ιMulti K k (fun j => (w j : V)) =
      bW.det w • ExteriorAlgebra.ιMulti K k (fun j => (bW j : V)) := by sorry
