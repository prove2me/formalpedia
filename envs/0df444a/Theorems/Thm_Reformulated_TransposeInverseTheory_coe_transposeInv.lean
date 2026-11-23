-- Prove2me | Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
-- name    : Reformulated.TransposeInverseTheory.coe_transposeInv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:27.378242+00:00
-- url     : https://prove2.me/theorems/a19b7aed-306c-4d14-bc5d-52544acd3b62
-- title:
--   Transpose Inverse Theory: coe transpose Inv
-- statement:
--   The Transpose Inverse Theory construction uses the coe transpose Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/TransposeInverse/TransposeInv.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/TransposeInverse/TransposeInv.lean#L32-L33

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

theorem Reformulated.TransposeInverseTheory.coe_transposeInv (g : GL n R) :
    ((transposeInv g : GL n R) : Matrix n n R) = ((g⁻¹ : GL n R) : Matrix n n R)ᵀ := by sorry

attribute [defeq] Reformulated.TransposeInverseTheory.coe_transposeInv
