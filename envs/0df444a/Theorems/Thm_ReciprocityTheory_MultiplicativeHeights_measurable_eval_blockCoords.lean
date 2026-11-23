-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurable_eval_blockCoords
-- name    : ReciprocityTheory.MultiplicativeHeights.measurable_eval_blockCoords
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:12.56851+00:00
-- url     : https://prove2.me/theorems/023d5ea8-3982-4273-9482-13fa5023dafd
-- title:
--   Multiplicative Heights: measurable eval block Coords
-- statement:
--   The Multiplicative Heights construction uses the measurable eval block Coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L32-L37

import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
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
open MeasureTheory MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.measurable_eval_blockCoords {B n : ℕ} (g : MvPolynomial (Fin B × Fin n) ℂ) :
    Measurable fun z : BlockSphere B n => eval (blockPoint z) g := by sorry
