-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultiDegreePositive_pos_of_isEmpty_e19be1779a19
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultiDegreePositive_pos_of_isEmpty_e19be1779a19
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:22.497888+00:00
-- url     : https://prove2.me/theorems/5838d5c2-eeb4-50b5-9f72-699c9a833f88
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Multi Degree Positive pos of is Empty e19be1779a19: P2 M Ground Theory Heights  Heights Hilbert Samuel Multi Degree Positive pos of is Empty e19be177
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Multi Degree Positive pos of is Empty e19be1779a19 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Multi Degree Positive pos of is Empty e19be1779a19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultiDegreePositive.lean#L42-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultiDegreePositive.lean#L42-L72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsMultiDegreePositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegrePrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegreHilb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegreDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegreePositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultiDegreePositive
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
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.MultiDegreePositive

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultiDegreePositive_pos_of_isEmpty_e19be1779a19 {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] [IsEmpty K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (e : ℕ) (hq : IsMultiProjPrime q)
    (hd : ringKrullDim (MRing ι F ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    0 < intNum F q (fun _ : Fin e => fun _ : K => (1 : ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MultiDegreePositive».«pos_of_isEmpty» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultiDegreePositive_pos_of_isEmpty_e19be1779a19
