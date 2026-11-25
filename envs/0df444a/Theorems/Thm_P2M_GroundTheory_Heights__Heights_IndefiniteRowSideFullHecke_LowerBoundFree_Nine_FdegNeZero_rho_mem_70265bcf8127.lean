-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_rho_mem_70265bcf8127
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_rho_mem_70265bcf8127
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:09.193593+00:00
-- url     : https://prove2.me/theorems/b2e332ce-aa01-578b-81e6-214068d9c838
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Nine Fdeg Ne Zero rho mem 70265bcf8127: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bou
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Nine Fdeg Ne Zero rho mem 70265bcf8127 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Lower Bound Free Nine Fdeg Ne Zero rho mem 70265bcf8127 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PTwinFdegNeZero.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PTwinFdegNeZero.lean#L96-L99

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_rho_mem_70265bcf8127 (j : ℕ) (hj : j ≤ N) (l : Ψ × Fin N) :
    (rho j hj l).1 = l.1 ∧ ((((rho j hj l).2 : Fin N) : ℕ) < j ↔ (l.2 : ℕ) < j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«LowerBoundFree».«Nine».«FdegNeZero».«rho_mem» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_rho_mem_70265bcf8127
