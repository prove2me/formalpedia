-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Cmp_norm_sub_lt_one_of_dense
-- name    : ReciprocityTheory.Neutral.Cmp.norm_sub_lt_one_of_dense
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:06:11.154905+00:00
-- url     : https://prove2.me/theorems/b2d732c5-881e-4553-923a-96e2acc82cbe
-- title:
--   Cmp: norm sub lt one of dense
-- statement:
--   The Cmp construction uses the norm sub lt one of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/Inertia.lean#L28-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/Inertia.lean#L28-L43

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

theorem ReciprocityTheory.Neutral.Cmp.norm_sub_lt_one_of_dense {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) (σ : GK F ι)
    (g : PadicAlgCl p → PadicAlgCl p)
    (hg : ∀ x y : PadicAlgCl p, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖g x - g y‖ ≤ ‖x - y‖)
    (H : ∀ b ∈ A, ‖σ (ι b) - g (ι b)‖ < 1) (x : PadicAlgCl p) (hx : ‖x‖ ≤ 1) :
    ‖σ x - g x‖ < 1 := by sorry
