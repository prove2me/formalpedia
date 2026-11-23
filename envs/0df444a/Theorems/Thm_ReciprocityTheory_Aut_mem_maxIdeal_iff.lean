-- Prove2me | Theorems.Thm_ReciprocityTheory_Aut_mem_maxIdeal_iff
-- name    : ReciprocityTheory.Aut.mem_maxIdeal_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:20:27.193912+00:00
-- url     : https://prove2.me/theorems/125b1c14-58d2-4834-b56d-b15297674676
-- title:
--   Aut: mem max Ideal iff
-- statement:
--   The Aut construction uses the mem max Ideal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Automorphisms/InstMainA.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Automorphisms/InstMainA.lean#L11-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Aut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem ReciprocityTheory.Aut.mem_maxIdeal_iff (x : v.adicCompletionIntegers F) :
    x ∈ maximalIdeal (v.adicCompletionIntegers F) ↔ Valued.v (x : v.adicCompletion F) < 1 := by sorry
