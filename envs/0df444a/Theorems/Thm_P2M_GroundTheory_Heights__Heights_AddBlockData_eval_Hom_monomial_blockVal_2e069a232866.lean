-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_eval_Hom_monomial_blockVal_2e069a232866
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockData_eval_Hom_monomial_blockVal_2e069a232866
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:16:09.368682+00:00
-- url     : https://prove2.me/theorems/0065b693-aaef-4ceb-bc09-ef40ad3690c9
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Data eval Hom monomial block Val 2e069a232866: P2 M Ground Theory Heights  Heights Add Block Data eval Hom monomial block Val 2e069a232866
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Data eval Hom monomial block Val 2e069a232866 construction uses the P2 M Ground Theory Heights  Heights Add Block Data eval Hom monomial block Val 2e069a232866 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExtMapLiftOldOfIsWeightedHomogeneous.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExtMapLiftOldOfIsWeightedHomogeneous.lean#L23-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExtMapLiftOldOfIsWeightedHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.AddBlockData
variable {P : ArithVariety n} (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_AddBlockData_eval_Hom_monomial_blockVal_2e069a232866 (d : Coord n →₀ ℕ) (r : ℤ) :
    eval₂Hom (Int.castRingHom (MvPolynomial (Option ι) P.FunField))
        (fun v : Coord n ↦ C (P.mkF (X v)) * X (some v.1)) (monomial d r) =
      C (P.mkF (monomial d r)) * ∏ k, X (some k) ^ (Finsupp.weight (coordDeg n) d k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockData».«eval₂Hom_monomial_blockVal» := P2M_GroundTheory_Heights__Heights_AddBlockData_eval_Hom_monomial_blockVal_2e069a232866
