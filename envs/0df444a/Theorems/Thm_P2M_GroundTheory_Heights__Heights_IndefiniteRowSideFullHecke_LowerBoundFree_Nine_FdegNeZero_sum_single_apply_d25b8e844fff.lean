-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_sum_single_apply_d25b8e844fff
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_sum_single_apply_d25b8e844fff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:08.84422+00:00
-- url     : https://prove2.me/theorems/8ce0d28c-306a-4193-9dcd-fae4dff1deaf
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Nine Fdeg Ne Zero sum single apply d25b8e844fff: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Nine Fdeg Ne Zero sum single apply d25b8e844fff construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Nine Fdeg Ne Zero sum single apply d25b8e844fff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PTwinFdegNeZero.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PTwinFdegNeZero.lean#L108-L111

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_sum_single_apply_d25b8e844fff (j : ℕ) (σ : Perm (Ψ × Fin N)) (l : Ψ × Fin N) :
    (∑ l', Finsupp.single (σ l') (colExp j N l'.2)) (σ l) = colExp j N l.2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«LowerBoundFree».«Nine».«FdegNeZero».«sum_single_apply» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_sum_single_apply_d25b8e844fff
