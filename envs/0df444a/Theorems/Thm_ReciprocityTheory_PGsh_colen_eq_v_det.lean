-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_colen_eq_v_det
-- name    : ReciprocityTheory.PGsh.colen_eq_v_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:48.739499+00:00
-- url     : https://prove2.me/theorems/6bba6c90-352e-49e2-bdb6-1a52f5290973
-- title:
--   PGsh: colen eq v det
-- statement:
--   The PGsh construction uses the colen eq v det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VDetEqOneOfIntegral.lean#L129-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VDetEqOneOfIntegral.lean#L129-L131

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
variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.PGsh.colen_eq_v_det (L' L : Lat v ι) : colen L' L = v (L.B⁻¹ * L'.B).det := by sorry
