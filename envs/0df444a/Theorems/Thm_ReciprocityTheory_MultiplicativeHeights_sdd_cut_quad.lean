-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_cut_quad
-- name    : ReciprocityTheory.MultiplicativeHeights.sdd_cut_quad
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:12.911354+00:00
-- url     : https://prove2.me/theorems/78d8279b-0683-5276-b470-1ddef2779eba
-- title:
--   Multiplicative Heights: sdd cut quad
-- statement:
--   The Multiplicative Heights construction uses the sdd cut quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L178-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L178-L191

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA
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
open Matrix NumberField
open scoped ComplexOrder MatrixOrder

theorem ReciprocityTheory.MultiplicativeHeights.sdd_cut_quad {r k : ℕ} (d : Fin r → ℝ) (hd : ∀ l, 0 ≤ d l) (e : ℕ)
    (E B1 : Matrix (Fin r) (Fin k) ℂ) (hB1 : ∀ l j, B1 l j = if e ≤ (l : ℕ) then E l j else 0)
    (v : Fin k → ℂ) :
    (star v ⬝ᵥ ((B1ᴴ * diagonal (fun l => (d l : ℂ)) * B1) *ᵥ v)).re ≤
      (star v ⬝ᵥ ((Eᴴ * diagonal (fun l => (d l : ℂ)) * E) *ᵥ v)).re := by sorry
