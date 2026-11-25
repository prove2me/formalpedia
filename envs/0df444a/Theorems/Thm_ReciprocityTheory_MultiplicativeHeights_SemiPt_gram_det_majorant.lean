-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_gram_det_majorant
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.gram_det_majorant
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:39.506583+00:00
-- url     : https://prove2.me/theorems/b3c99f4d-5bd1-4782-b62d-54ab257a7b61
-- title:
--   Semi Pt: gram det majorant
-- statement:
--   The Semi Pt construction uses the gram det majorant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegZA.lean#L14-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegZA.lean#L14-L47

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZ
import Definitions.Def_Lemmata_GeneralBFactSecondAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZA
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.gram_det_majorant {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (M : Majorant S) (hG : S.G.det ≠ 0) (σ : K →+* ℂ) (b : Fin r → Fin r → K) :
    (gramC (M.H σ) σ b).det.re = ‖σ (hGram S b).det‖ := by sorry
