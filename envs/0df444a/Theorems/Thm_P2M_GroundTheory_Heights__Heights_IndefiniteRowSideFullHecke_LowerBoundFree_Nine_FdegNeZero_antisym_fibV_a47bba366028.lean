-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_antisym_fibV_a47bba366028
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_antisym_fibV_a47bba366028
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:02.22252+00:00
-- url     : https://prove2.me/theorems/be1f1c02-82c4-4662-81e1-c0f055f634f5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Nine Fdeg Ne Zero antisym fib V a47bba366028: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Low
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Nine Fdeg Ne Zero antisym fib V a47bba366028 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Nine Fdeg Ne Zero antisym fib V a47bba366028 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PTwinFdegNeZero.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PTwinFdegNeZero.lean#L74-L79

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_antisym_fibV_a47bba366028 (j : ℕ) (hj : j ≤ N) :
    antisym (G0 j) (fibV (Ψ := Ψ) j hj) = ((G0 (Ψ := Ψ) (N := N) j).card : ℚ) • fibV j hj := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«LowerBoundFree».«Nine».«FdegNeZero».«antisym_fibV» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_antisym_fibV_a47bba366028
