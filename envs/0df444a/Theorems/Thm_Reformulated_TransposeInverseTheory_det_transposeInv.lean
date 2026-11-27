-- Prove2me | Theorems.Thm_Reformulated_TransposeInverseTheory_det_transposeInv
-- name    : Reformulated.TransposeInverseTheory.det_transposeInv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:32:14.484626+00:00
-- url     : https://prove2.me/theorems/b5b2f24e-2a5b-51b7-a606-7f6e1dbfe264
-- title:
--   Transpose Inverse Theory: det transpose Inv
-- statement:
--   The Transpose Inverse Theory construction uses the det transpose Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/TransposeInverse/TransposeInv.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/TransposeInverse/TransposeInv.lean#L46-L50

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

theorem Reformulated.TransposeInverseTheory.det_transposeInv (g : GL n R) :
    GeneralLinearGroup.det (transposeInv g) = (GeneralLinearGroup.det g)⁻¹ := by sorry
