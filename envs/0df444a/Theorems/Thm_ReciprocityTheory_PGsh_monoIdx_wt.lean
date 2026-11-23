-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_monoIdx_wt
-- name    : ReciprocityTheory.PGsh.monoIdx_wt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:42.207808+00:00
-- url     : https://prove2.me/theorems/73ead648-0c5e-459a-b217-2184cf6eae41
-- title:
--   PGsh: mono Idx wt
-- statement:
--   The PGsh construction uses the mono Idx wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/QExpansionMonoWCoeffZero.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/QExpansionMonoWCoeffZero.lean#L14-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Eisenstein4CoeffBound
import Definitions.Def_ReciprocityTheory_DualLattices_QExpansionMonoWCoeffZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open UpperHalfPlane hiding I
open Complex ModularForm ModularFormClass MatrixGroups EisensteinSeries

theorem ReciprocityTheory.PGsh.monoIdx_wt {w a : ℕ} (h : a ∈ monoIdx w) : 4 * a + 6 * monoB w a = w := by sorry
