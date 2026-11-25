-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wVal_adMet
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.wVal_adMet
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:23.966828+00:00
-- url     : https://prove2.me/theorems/b1bba758-c49d-4571-b588-5e6916ec5401
-- title:
--   Semi Pt: w Val ad Met
-- statement:
--   The Semi Pt construction uses the w Val ad Met property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegF.lean#L104-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegF.lean#L104-L147

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.wVal_adMet {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K)
    (dd : Fin r → ℝ) (h2m : 2 * m ≤ r)
    (hg : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0) (σ : K →+* ℂ)
    (hreal : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → conj (σ (g i)) = σ (g i))
    (i : Fin r) :
    σ (wVal r m g i) * (((adMet r m g dd σ (wPart r m i) : ℝ) : ℂ))⁻¹ *
      σ (wVal r m g (wPart r m i)) = ((adMet r m g dd σ i : ℝ) : ℂ) := by sorry
