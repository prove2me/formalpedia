-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_quad_mul
-- name    : ReciprocityTheory.MultiplicativeHeights.sc_quad_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:48.747792+00:00
-- url     : https://prove2.me/theorems/d7dec83a-e9a4-4768-a241-4d0d76494e72
-- title:
--   Multiplicative Heights: sc quad mul
-- statement:
--   The Multiplicative Heights construction uses the sc quad mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractA.lean#L124-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractA.lean#L124-L127

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.sc_quad_mul {r : Type*} [Fintype r] (H M : Matrix r r ℂ) (u : r → ℂ) :
    star u ⬝ᵥ ((Mᴴ * H * M) *ᵥ u) = star (M *ᵥ u) ⬝ᵥ (H *ᵥ (M *ᵥ u)) := by sorry
