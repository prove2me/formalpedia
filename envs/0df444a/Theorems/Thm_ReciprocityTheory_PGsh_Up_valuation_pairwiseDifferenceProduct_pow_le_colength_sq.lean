-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_valuation_pairwiseDifferenceProduct_pow_le_colength_sq
-- name    : ReciprocityTheory.PGsh.Up.valuation_pairwiseDifferenceProduct_pow_le_colength_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:49.006715+00:00
-- url     : https://prove2.me/theorems/20a660d0-bee3-45b9-ba45-cdbc78bca2e6
-- title:
--   Up: valuation pairwise Difference Product pow le colength sq
-- statement:
--   The Up construction uses the valuation pairwise Difference Product pow le colength sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationPairwiseDifferenceProductPowLeColengthS.lean#L209-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationPairwiseDifferenceProductPowLeColengthS.lean#L209-L360

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
open DeterminantValuationBounds

theorem ReciprocityTheory.PGsh.Up.valuation_pairwiseDifferenceProduct_pow_le_colength_sq (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (n : ℕ)
    (a : Fin n → C) (s : ℕ) (M S : Lat v (Fin n × Fin s)) (Mτ : Fin n → Lat v (Fin s))
    (hM : IsLaStable a M) (hτ : ∀ τ, (Mτ τ).pts = projPts M.pts τ) (hS : S.pts = sumPts Mτ) :
    v (discr a) ^ s ≤ colen M S ^ 2 := by sorry
