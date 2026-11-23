-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_evalT_zero
-- name    : ReciprocityTheory.PGsh.evalT_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:49.879864+00:00
-- url     : https://prove2.me/theorems/c29c1574-f513-46ce-a433-46009fbfa8cb
-- title:
--   PGsh: eval T zero
-- statement:
--   The PGsh construction uses the eval T zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L273-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean#L273-L276

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
variable {M : Type u} [AddCommGroup M] [Module R₀ M]

theorem ReciprocityTheory.PGsh.evalT_zero {A : Type u} [CommRing A] [Algebra R₀ A] (H : M →ₗ[R₀] A) (K : Submodule R₀ A) :
    evalT H K 0 = 0 := by sorry
