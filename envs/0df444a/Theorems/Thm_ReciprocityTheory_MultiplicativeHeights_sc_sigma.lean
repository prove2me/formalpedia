-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_sigma
-- name    : ReciprocityTheory.MultiplicativeHeights.sc_sigma
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:40:40.554874+00:00
-- url     : https://prove2.me/theorems/e6616348-7e74-4386-8cf5-67ac1ccbcf33
-- title:
--   Multiplicative Heights: sc sigma
-- statement:
--   The Multiplicative Heights construction uses the sc sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractA.lean#L143-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractA.lean#L143-L198

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

theorem ReciprocityTheory.MultiplicativeHeights.sc_sigma {r k m : Type*} [Fintype r] [Fintype k] [Fintype m] [DecidableEq k]
    [DecidableEq m] [Nonempty m] {H M : Matrix r r ℂ} (hH : H.PosDef)
    (hM : ∀ u : r → ℂ, u ≠ 0 → (star (M *ᵥ u) ⬝ᵥ (H *ᵥ (M *ᵥ u))).re < (star u ⬝ᵥ (H *ᵥ u)).re)
    (Bm : Matrix r k ℂ) (Cm : Matrix r m ℂ) (hW : Function.Injective (fromCols Bm Cm).mulVec)
    (hMB : M * Bm = 0) (hMC : Function.Injective (M * Cm).mulVec) :
    0 < ((M * Cm)ᴴ * H * (M * Cm)).det.re ∧ ((M * Cm)ᴴ * H * (M * Cm)).det.re <
      (Cmᴴ * H * Cm - (Cmᴴ * H * Bm) * (Bmᴴ * H * Bm)⁻¹ * (Bmᴴ * H * Cm)).det.re := by sorry
