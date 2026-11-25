-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_relDim_eq_zero_of_ringKrullDim_47c8ef99c9a9
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_relDim_eq_zero_of_ringKrullDim_47c8ef99c9a9
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:48:32.877634+00:00
-- url     : https://prove2.me/theorems/5d70de66-e43c-510f-975d-80390ad59535
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel rel Dim eq zero of ring Krull Dim 47c8ef99c9a9: P2 M Ground Theory Heights  Heights Hilbert Samuel rel Dim eq zero of ring Krull Dim 47c8ef99c9a9
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel rel Dim eq zero of ring Krull Dim 47c8ef99c9a9 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel rel Dim eq zero of ring Krull Dim 47c8ef99c9a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertDimZero.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertDimZero.lean#L16-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertDimZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
universe u

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_relDim_eq_zero_of_ringKrullDim_47c8ef99c9a9 {F : Type*} [Field F] {K : Type} [Fintype K]
    {ι : K → Type} (q : Ideal (MRing ι F))
    (hd : ringKrullDim (MRing ι F ⧸ q) = ((Fintype.card K : ℕ) : WithBot ℕ∞)) :
    GroundTheory.Heights₂.Heights.FieldNumbers.relDim q = ((0 : ℕ) : WithBot (WithTop ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«relDim_eq_zero_of_ringKrullDim» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_relDim_eq_zero_of_ringKrullDim_47c8ef99c9a9
