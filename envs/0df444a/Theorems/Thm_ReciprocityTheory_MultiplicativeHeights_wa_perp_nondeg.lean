-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_perp_nondeg
-- name    : ReciprocityTheory.MultiplicativeHeights.wa_perp_nondeg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:16.267794+00:00
-- url     : https://prove2.me/theorems/59fa0ab1-0e6c-4636-b426-b8276f38c399
-- title:
--   Multiplicative Heights: wa perp nondeg
-- statement:
--   The Multiplicative Heights construction uses the wa perp nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L150-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L150-L175

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module

theorem ReciprocityTheory.MultiplicativeHeights.wa_perp_nondeg {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (W : Submodule K (Fin r → K)) (hnd : ∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0)
    (x y : Fin r → K) (hxW : x ∈ W) (hyW : y ∈ W) (hxx : S.h x x = 0) (hxy : S.h x y = 1)
    (hyy : S.h y y = 0) :
    ∀ z ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y),
      (∀ w ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y), S.h z w = 0) → z = 0 := by sorry
