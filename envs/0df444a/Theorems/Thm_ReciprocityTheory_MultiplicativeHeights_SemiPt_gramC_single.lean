-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_gramC_single
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.gramC_single
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:02:42.823954+00:00
-- url     : https://prove2.me/theorems/96bbffeb-fe14-4a7a-a429-80d17970dd14
-- title:
--   Semi Pt: gram C single
-- statement:
--   The Semi Pt construction uses the gram C single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegR.lean#L13-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegR.lean#L13-L31

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegT
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegR
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.gramC_single {K : Type} [Field K] [NumberField K] {r : ℕ} (δ : (K →+* ℂ) → Fin r → ℝ)
    (σ : K →+* ℂ) (i : Fin r) (x : Fin r → K) (hx : IsAt i x) :
    (gramC (diagMet δ σ) σ ![x]).det.re = ‖σ (x i)‖ ^ 2 * δ σ i := by sorry
