-- Prove2me | Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_apply
-- name    : Reformulated.TransposeInverseTheory.transposeInv_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:32:36.85147+00:00
-- url     : https://prove2.me/theorems/37b4a5e7-de1f-4638-b764-afce94540fca
-- title:
--   Transpose Inverse Theory: transpose Inv apply
-- statement:
--   The Transpose Inverse Theory construction uses the transpose Inv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/TransposeInverse/TransposeInv.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/TransposeInverse/TransposeInv.lean#L38-L39

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

theorem Reformulated.TransposeInverseTheory.transposeInv_apply (g : GL n R) (i j : n) :
    (transposeInv g : GL n R) i j = (g⁻¹ : GL n R) j i := by sorry
