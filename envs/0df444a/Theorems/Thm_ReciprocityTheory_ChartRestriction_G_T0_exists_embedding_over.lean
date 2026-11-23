-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_exists_embedding_over
-- name    : ReciprocityTheory.ChartRestriction.G.T0.exists_embedding_over
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:00.502369+00:00
-- url     : https://prove2.me/theorems/28e54e33-804f-4d1d-bcc2-a02c005a9a3d
-- title:
--   T0: exists embedding over
-- statement:
--   The T0 construction uses the exists embedding over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PTNonempty.lean#L34-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PTNonempty.lean#L34-L94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PTNonempty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField Cardinal

theorem ReciprocityTheory.ChartRestriction.G.T0.exists_embedding_over {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (hfg : (⊤ : IntermediateField K Ω).FG) (sg : K →+* ℂ) :
    ∃ P : Ω →+* ℂ, P.comp (algebraMap K Ω) = sg := by sorry
