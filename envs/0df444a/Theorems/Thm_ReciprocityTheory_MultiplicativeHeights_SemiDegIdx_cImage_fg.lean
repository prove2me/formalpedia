-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_cImage_fg
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.cImage_fg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:01:34.937795+00:00
-- url     : https://prove2.me/theorems/7c319c20-6420-4042-b18b-a23bc042f2a4
-- title:
--   Semi Deg Idx: c Image fg
-- statement:
--   The Semi Deg Idx construction uses the c Image fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCC.lean#L48-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegCC.lean#L48-L71

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCB
import Definitions.Def_Lemmata_MiscLemmasR_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.cImage_fg {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (C : Submodule (𝓞 K) K) (hC : C.FG) : (cImage c C).FG := by sorry
