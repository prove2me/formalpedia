-- Prove2me | Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv_inv
-- name    : Reformulated.TransposeInverseTheory.coe_transposeInv_inv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:32:25.764743+00:00
-- url     : https://prove2.me/theorems/3bc407e3-58ef-4678-a299-5dcd34973cdc
-- title:
--   Transpose Inverse Theory: coe transpose Inv inv
-- statement:
--   The Transpose Inverse Theory construction uses the coe transpose Inv inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/TransposeInverse/TransposeInv.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/TransposeInverse/TransposeInv.lean#L35-L36

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_TransposeInverse_TransposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Reformulated Reformulated.TransposeInverseTheory
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

theorem Reformulated.TransposeInverseTheory.coe_transposeInv_inv (g : GL n R) :
    (((transposeInv g)⁻¹ : GL n R) : Matrix n n R) = (g : Matrix n n R)ᵀ := by sorry
