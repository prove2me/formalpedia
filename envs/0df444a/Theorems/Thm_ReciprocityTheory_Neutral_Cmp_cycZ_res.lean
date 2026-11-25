-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_cycZ_res
-- name    : ReciprocityTheory.Neutral.Cmp.cycZ_res
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:39:53.679269+00:00
-- url     : https://prove2.me/theorems/615d7f8c-fd5c-4180-9581-438e25e7d39c
-- title:
--   Cmp: cyc Z res
-- statement:
--   The Cmp construction uses the cyc Z res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/Inertia.lean#L58-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/Inertia.lean#L58-L78

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

theorem ReciprocityTheory.Neutral.Cmp.cycZ_res (ι : Ω →+* PadicAlgCl p) (l : ℕ) [Fact l.Prime] (σ : GK F ι) :
    cycZ F Ω l (res ι σ) = cyclotomicCharacter (PadicAlgCl p) l (σ : PadicAlgCl p ≃+* PadicAlgCl p) := by sorry
