-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_gram_posSemidef
-- name    : ReciprocityTheory.MultiplicativeHeights.approxB_gram_posSemidef
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:27.702902+00:00
-- url     : https://prove2.me/theorems/7f0ca44d-b64f-5cdc-ac12-a663d93ca1be
-- title:
--   Multiplicative Heights: approx B gram pos Semidef
-- statement:
--   The Multiplicative Heights construction uses the approx B gram pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L156-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L156-L176

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
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
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.approxB_gram_posSemidef {r p : ℕ} {ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ : 0 < ρ) (X : Fin r → Fin r → ℂ)
    (hg : ∀ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
      negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j))) :
    (Matrix.of fun k j : ApproxPosIdx r p => jForm p (X k.1) (X j.1)).PosSemidef := by sorry
