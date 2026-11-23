-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_res_mem_dec
-- name    : ReciprocityTheory.Neutral.Cmp.res_mem_dec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:39.161809+00:00
-- url     : https://prove2.me/theorems/6f4f6a2b-ce55-4e7b-a094-99251ccfa055
-- title:
--   Cmp: res mem dec
-- statement:
--   The Cmp construction uses the res mem dec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ContinuousGK.lean#L90-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ContinuousGK.lean#L90-L102

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ValuationIntCastLtOneIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ContinuousGK
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
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Pointwise
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

theorem ReciprocityTheory.Neutral.Cmp.res_mem_dec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) (σ : GK F ι) :
    res ι σ ∈ Dec (F := F) A := by sorry
