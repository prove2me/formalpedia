-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_DeterminantValuationBounds_v_det_le_of_cols
-- name    : ReciprocityTheory.PGsh.Up.DeterminantValuationBounds.v_det_le_of_cols
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:06:27.459166+00:00
-- url     : https://prove2.me/theorems/31cfdafb-6b5a-4248-a9b6-d88e67599910
-- title:
--   Determinant Valuation Bounds: v det le of cols
-- statement:
--   The Determinant Valuation Bounds construction uses the v det le of cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationPairwiseDifferenceProductPowLeColengthS.lean#L192-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationPairwiseDifferenceProductPowLeColengthS.lean#L192-L203

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
variable {n s : ℕ}

theorem ReciprocityTheory.PGsh.Up.DeterminantValuationBounds.v_det_le_of_cols {ι : Type} [Fintype ι] [DecidableEq ι] (L : Lat v ι) (X : Matrix ι ι C)
    (hX : ∀ y, (fun x => X x y) ∈ L.pts) : v X.det ≤ v L.B.det := by sorry
