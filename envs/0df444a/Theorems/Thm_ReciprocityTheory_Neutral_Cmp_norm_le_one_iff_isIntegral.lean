-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_norm_le_one_iff_isIntegral
-- name    : ReciprocityTheory.Neutral.Cmp.norm_le_one_iff_isIntegral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:41.668803+00:00
-- url     : https://prove2.me/theorems/af067b08-5494-482e-98a2-5491fb80d514
-- title:
--   Cmp: norm le one iff is Integral
-- statement:
--   The Cmp construction uses the norm le one iff is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/Inertia.lean#L80-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/Inertia.lean#L80-L114

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ContinuousGK
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Inertia
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

theorem ReciprocityTheory.Neutral.Cmp.norm_le_one_iff_isIntegral (x : PadicAlgCl p) : ‖x‖ ≤ 1 ↔ IsIntegral (PadicInt.subring p) x := by sorry
