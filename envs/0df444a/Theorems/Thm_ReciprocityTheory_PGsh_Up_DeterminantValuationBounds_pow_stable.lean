-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_DeterminantValuationBounds_pow_stable
-- name    : ReciprocityTheory.PGsh.Up.DeterminantValuationBounds.pow_stable
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:50.859804+00:00
-- url     : https://prove2.me/theorems/0209cbd9-ac3b-49e3-811f-75c2c46ed66e
-- title:
--   Determinant Valuation Bounds: pow stable
-- statement:
--   The Determinant Valuation Bounds construction uses the pow stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationPairwiseDifferenceProductPowLeColengthS.lean#L179-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationPairwiseDifferenceProductPowLeColengthS.lean#L179-L190

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

theorem ReciprocityTheory.PGsh.Up.DeterminantValuationBounds.pow_stable {a : Fin n → C} {M : Lat v (Fin n × Fin s)} (hM : IsLaStable a M) (k : ℕ)
    {w : Fin n × Fin s → C} (hw : w ∈ M.pts) :
    (fun y : Fin n × Fin s => a y.1 ^ k * w y) ∈ M.pts := by sorry
