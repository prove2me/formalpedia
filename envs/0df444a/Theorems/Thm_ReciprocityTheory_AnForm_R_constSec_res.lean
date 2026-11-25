-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_constSec_res
-- name    : ReciprocityTheory.AnForm.R.constSec_res
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:59.037994+00:00
-- url     : https://prove2.me/theorems/c1a52b0a-1cfe-5947-b17b-fb1eec707b7f
-- title:
--   R: const Sec res
-- statement:
--   The R construction uses the const Sec res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L81-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L81-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
variable {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of ℂ))

theorem ReciprocityTheory.AnForm.R.constSec_res (U : S.Opens) (c : ℂ) :
    constSec s U c = S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (constSec s ⊤ c) := by sorry
