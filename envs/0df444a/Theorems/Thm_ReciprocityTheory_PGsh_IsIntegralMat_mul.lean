-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mul
-- name    : ReciprocityTheory.PGsh.IsIntegralMat.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:50.436183+00:00
-- url     : https://prove2.me/theorems/f2377a60-47c3-4fa7-981f-75abebf0237b
-- title:
--   Is Integral Mat: mul
-- statement:
--   The Is Integral Mat construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VDetEqOneOfIntegral.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VDetEqOneOfIntegral.lean#L36-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_NearIdentityColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open Matrix
variable {K : Type} [Field K] (v : Valuation K NNReal) {ι : Type} [Fintype ι] [DecidableEq ι]
variable {v}

theorem ReciprocityTheory.PGsh.IsIntegralMat.mul {U V : Matrix ι ι K} (hU : IsIntegralMat v U)
    (hV : IsIntegralMat v V) : IsIntegralMat v (U * V) := by sorry
