-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_hypForm_h
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.hypForm_h
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:02:57.851918+00:00
-- url     : https://prove2.me/theorems/17512806-4c28-4d3c-b131-4c0aa821b8cc
-- title:
--   Semi Pt: hyp Form h
-- statement:
--   The Semi Pt construction uses the hyp Form h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegI.lean#L24-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegI.lean#L24-L35

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegH
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegI
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.hypForm_h {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (j p : Fin r)
    (x y : Fin r → K) : (hypForm S j p).h x y = S.c (x j) * y p + S.c (x p) * y j := by sorry
