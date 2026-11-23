-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_infinite_residues
-- name    : ReciprocityTheory.MultiplicativeHeights.infinite_residues
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:28.758234+00:00
-- url     : https://prove2.me/theorems/ce589a92-004e-48c7-9d79-f0d160125a1d
-- title:
--   Multiplicative Heights: infinite residues
-- statement:
--   The Multiplicative Heights construction uses the infinite residues property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExistsTorusPointOneLeNormSum.lean#L45-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExistsTorusPointOneLeNormSum.lean#L45-L71

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsTorusPointOneLeNormSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.infinite_residues {K : Type*} [NormedField K] [IsUltrametricDist K] (K₀ : Subfield K)
    (hK₀ : ResidueFieldInfiniteOn (K₀ : Set K)) :
    {y : IsLocalRing.ResidueField (unitBallRing K) | ∃ x : unitBallRing K,
      (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y}.Infinite := by sorry
