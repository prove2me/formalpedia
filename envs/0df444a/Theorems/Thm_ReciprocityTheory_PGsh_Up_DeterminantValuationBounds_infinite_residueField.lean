-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_DeterminantValuationBounds_infinite_residueField
-- name    : ReciprocityTheory.PGsh.Up.DeterminantValuationBounds.infinite_residueField
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:06:35.20266+00:00
-- url     : https://prove2.me/theorems/ed46d031-9a52-4ff6-aed5-a0b16a2b85c3
-- title:
--   Determinant Valuation Bounds: infinite residue Field
-- statement:
--   The Determinant Valuation Bounds construction uses the infinite residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationPairwiseDifferenceProductPowLeColengthS.lean#L15-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationPairwiseDifferenceProductPowLeColengthS.lean#L15-L57

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationPairwiseDifferenceProductPowLeColengthS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
open ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
variable {C : Type} [Field C] {v : Valuation C NNReal}

theorem ReciprocityTheory.PGsh.Up.DeterminantValuationBounds.infinite_residueField [IsAlgClosed C] :
    Infinite (IsLocalRing.ResidueField v.valuationSubring) := by sorry
