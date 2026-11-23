-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_det_le_one
-- name    : ReciprocityTheory.PGsh.IsIntegralMat.det_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:41.294728+00:00
-- url     : https://prove2.me/theorems/eedd622b-4ce5-4f45-a1bb-93874166f9e0
-- title:
--   Is Integral Mat: det le one
-- statement:
--   The Is Integral Mat construction uses the det le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VDetEqOneOfIntegral.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VDetEqOneOfIntegral.lean#L18-L25

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

theorem ReciprocityTheory.PGsh.IsIntegralMat.det_le_one {U : Matrix ι ι K} (hU : IsIntegralMat v U) : v U.det ≤ 1 := by sorry
