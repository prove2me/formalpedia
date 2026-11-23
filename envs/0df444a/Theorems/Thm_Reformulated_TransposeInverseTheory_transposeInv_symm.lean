-- Prove2me | Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
-- name    : Reformulated.TransposeInverseTheory.transposeInv_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:31.348281+00:00
-- url     : https://prove2.me/theorems/696f9926-264d-4ec6-b30a-a703e24b362b
-- title:
--   Transpose Inverse Theory: transpose Inv symm
-- statement:
--   The Transpose Inverse Theory construction uses the transpose Inv symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/TransposeInverse/TransposeInv.lean#L44-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/TransposeInverse/TransposeInv.lean#L44-L44

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

theorem Reformulated.TransposeInverseTheory.transposeInv_symm : (transposeInv : GL n R ≃* GL n R).symm = transposeInv := by sorry

attribute [defeq] Reformulated.TransposeInverseTheory.transposeInv_symm
