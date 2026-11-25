-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_det_blkMat_467515454fff
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_det_blkMat_467515454fff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:23:51.6948+00:00
-- url     : https://prove2.me/theorems/96b0e062-2507-4000-af21-cfb5b09fa429
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Nine Fdeg Ne Zero det blk Mat 467515454fff: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Nine Fdeg Ne Zero det blk Mat 467515454fff construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Nine Fdeg Ne Zero det blk Mat 467515454fff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PTwinFdegNeZero.lean#L24-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PTwinFdegNeZero.lean#L24-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PTwinFdegNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
open MvPolynomial Matrix Equiv
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FdegNeZero
variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}
omit [Fintype Ψ] [DecidableEq Ψ]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_det_blkMat_467515454fff (j : ℕ) (hj : j ≤ N) (τ : Ψ) :
    (blkMat (Ψ := Ψ) (N := N) j τ).det = altRho j (yv j hj τ) * altRho (N - j) (zv j τ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«LowerBoundFree».«Nine».«FdegNeZero».«det_blkMat» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_det_blkMat_467515454fff
