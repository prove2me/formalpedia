-- Prove2me | Theorems.Thm_ReciprocityTheory_GC_burnside_surj_of_irred
-- name    : ReciprocityTheory.GC.burnside_surj_of_irred
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:52:28.152711+00:00
-- url     : https://prove2.me/theorems/917ea2f5-be46-4ee4-b69d-4f92a747b49e
-- title:
--   GC: burnside surj of irred
-- statement:
--   The GC construction uses the burnside surj of irred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/BurnsideSurjectivity/Burnside.lean#L170-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/BurnsideSurjectivity/Burnside.lean#L170-L176

import Mathlib
import Definitions.Def_ReciprocityTheory_BurnsideSurjectivity_Burnside
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GC

theorem ReciprocityTheory.GC.burnside_surj_of_irred {k A V : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : A →ₐ[k] Module.End k V) [Nontrivial V]
    (hirr : ∀ W : Submodule k V, (∀ a : A, ∀ w ∈ W, ρ a w ∈ W) → W = ⊥ ∨ W = ⊤) : Function.Surjective ρ := by sorry
