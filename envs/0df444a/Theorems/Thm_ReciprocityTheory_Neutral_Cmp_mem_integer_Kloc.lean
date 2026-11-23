-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_mem_integer_Kloc
-- name    : ReciprocityTheory.Neutral.Cmp.mem_integer_Kloc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:42.749987+00:00
-- url     : https://prove2.me/theorems/761c0c52-fa01-43df-864b-247ebf8aaf96
-- title:
--   Cmp: mem integer Kloc
-- statement:
--   The Cmp construction uses the mem integer Kloc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelA.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelA.lean#L40-L45

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA
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
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
attribute [local instance] locRel

theorem ReciprocityTheory.Neutral.Cmp.mem_integer_Kloc (ι : Ω →+* PadicAlgCl p) (x : Kloc F ι) :
    x ∈ 𝒪[Kloc F ι] ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := by sorry
