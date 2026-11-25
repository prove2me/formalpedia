-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_coe_mem_monoSpanF
-- name    : ReciprocityTheory.PGsh.coe_mem_monoSpanF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:51.115188+00:00
-- url     : https://prove2.me/theorems/7d6e8f1e-3d19-4f94-ad28-9485409eeb8f
-- title:
--   PGsh: coe mem mono Span F
-- statement:
--   The PGsh construction uses the coe mem mono Span F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/QExpansionMonoWCoeffZero.lean#L89-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/QExpansionMonoWCoeffZero.lean#L89-L125

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

theorem ReciprocityTheory.PGsh.coe_mem_monoSpanF (w : ℕ) (f : ModularForm 𝒮ℒ (w : ℤ)) : (⇑f : ℍ → ℂ) ∈ monoSpanF w := by sorry
