-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_gramC_eq
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.gramC_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:32.454849+00:00
-- url     : https://prove2.me/theorems/69e0b72e-2e18-4b28-b2a1-9f7d23086fd6
-- title:
--   Semi Pt: gram C eq
-- statement:
--   The Semi Pt construction uses the gram C eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegE.lean#L200-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegE.lean#L200-L205

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.gramC_eq {K : Type} [Field K] [NumberField K] {r k : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    gramC H σ b = (embMat σ b)ᴴ * H * embMat σ b := by sorry
