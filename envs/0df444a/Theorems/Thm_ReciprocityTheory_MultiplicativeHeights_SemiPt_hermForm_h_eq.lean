-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_hermForm_h_eq
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.hermForm_h_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:20.869895+00:00
-- url     : https://prove2.me/theorems/bdb55439-163b-4a8b-90c1-0498d5199090
-- title:
--   Semi Pt: herm Form h eq
-- statement:
--   The Semi Pt construction uses the herm Form h eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegT.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegT.lean#L74-L77

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegG
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegT
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.hermForm_h_eq {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : S.h x y = formM S.c S.G x y := by sorry
