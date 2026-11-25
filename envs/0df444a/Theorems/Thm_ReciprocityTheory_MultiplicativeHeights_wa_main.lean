-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_main
-- name    : ReciprocityTheory.MultiplicativeHeights.wa_main
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:42.324624+00:00
-- url     : https://prove2.me/theorems/c052f854-e647-49a2-ad95-12a305ef493b
-- title:
--   Multiplicative Heights: wa main
-- statement:
--   The Multiplicative Heights construction uses the wa main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAB.lean#L39-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAB.lean#L39-L137

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAB
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

theorem ReciprocityTheory.MultiplicativeHeights.wa_main {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) :
    ∀ (n : ℕ) (W : Submodule K (Fin r → K)), finrank K W = n →
      (∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0) →
      ∃ (m : ℕ) (b : Fin n → Fin r → K) (g : Fin n → K), (∀ i, b i ∈ W) ∧ 2 * m ≤ n ∧
        (∀ i j, S.h (b i) (b j) = wittMat n m g i j) ∧
        ∀ t : Fin n → K, (∀ i : Fin n, (i : ℕ) < m ∨ n ≤ (i : ℕ) + m → t i = 0) →
          ∑ i, S.c (t i) * g i * t i = 0 → t = 0 := by sorry
