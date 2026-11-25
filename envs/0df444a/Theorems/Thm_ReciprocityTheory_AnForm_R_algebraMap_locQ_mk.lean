-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_algebraMap_locQ_mk
-- name    : ReciprocityTheory.AnForm.R.algebraMap_locQ_mk
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:28:44.165432+00:00
-- url     : https://prove2.me/theorems/1fe8b067-3655-4ae0-90ac-f1f641f28674
-- title:
--   R: algebra Map loc Q mk
-- statement:
--   The R construction uses the algebra Map loc Q mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypStalk.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypStalk.lean#L36-L39

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypStalk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {σ : Type}

theorem ReciprocityTheory.AnForm.R.algebraMap_locQ_mk (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) (f : MvPolynomial σ ℂ) :
    algebraMap (MvPolynomial σ ℂ ⧸ I) (locQ I z) (Ideal.Quotient.mk I f) =
      algebraMap _ (locQ I z) f := by sorry
