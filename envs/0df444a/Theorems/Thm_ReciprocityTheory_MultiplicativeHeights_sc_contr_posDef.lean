-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_contr_posDef
-- name    : ReciprocityTheory.MultiplicativeHeights.sc_contr_posDef
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:05:00.050806+00:00
-- url     : https://prove2.me/theorems/2b3b9081-0924-414f-a7b7-796c3a9eeadd
-- title:
--   Multiplicative Heights: sc contr pos Def
-- statement:
--   The Multiplicative Heights construction uses the sc contr pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractA.lean#L129-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractA.lean#L129-L141

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

theorem ReciprocityTheory.MultiplicativeHeights.sc_contr_posDef {r : Type*} [Fintype r] {H M : Matrix r r ℂ} (hH : H.PosDef)
    (hM : ∀ u : r → ℂ, u ≠ 0 → (star (M *ᵥ u) ⬝ᵥ (H *ᵥ (M *ᵥ u))).re < (star u ⬝ᵥ (H *ᵥ u)).re) :
    (H - Mᴴ * H * M).PosDef := by sorry
