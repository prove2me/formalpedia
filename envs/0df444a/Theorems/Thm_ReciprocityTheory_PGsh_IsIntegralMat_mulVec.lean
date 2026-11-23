-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec
-- name    : ReciprocityTheory.PGsh.IsIntegralMat.mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:40.884174+00:00
-- url     : https://prove2.me/theorems/f4450fc2-a0c2-4fe4-9fae-2ab832f95ada
-- title:
--   Is Integral Mat: mul Vec
-- statement:
--   The Is Integral Mat construction uses the mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VDetEqOneOfIntegral.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VDetEqOneOfIntegral.lean#L30-L34

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

theorem ReciprocityTheory.PGsh.IsIntegralMat.mulVec {U : Matrix ι ι K} {c : ι → K} (hU : IsIntegralMat v U)
    (hc : IsIntegralVec v c) : IsIntegralVec v (U *ᵥ c) := by sorry
