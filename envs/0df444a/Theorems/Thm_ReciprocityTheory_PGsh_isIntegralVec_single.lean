-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_isIntegralVec_single
-- name    : ReciprocityTheory.PGsh.isIntegralVec_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:28.256598+00:00
-- url     : https://prove2.me/theorems/00c67f3a-bfa7-408d-a471-a85c4465f467
-- title:
--   PGsh: is Integral Vec single
-- statement:
--   The PGsh construction uses the is Integral Vec single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VDetEqOneOfIntegral.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VDetEqOneOfIntegral.lean#L42-L46

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

theorem ReciprocityTheory.PGsh.isIntegralVec_single (j : ι) : IsIntegralVec v (Pi.single j (1 : K)) := by sorry
