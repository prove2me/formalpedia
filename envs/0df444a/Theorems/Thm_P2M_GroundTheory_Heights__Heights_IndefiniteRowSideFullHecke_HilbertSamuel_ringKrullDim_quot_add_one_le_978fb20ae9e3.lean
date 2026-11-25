-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_ringKrullDim_quot_add_one_le_978fb20ae9e3
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_ringKrullDim_quot_add_one_le_978fb20ae9e3
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:01:27.956503+00:00
-- url     : https://prove2.me/theorems/eb94cd3d-d36f-4f20-8737-9a58c7c66cbc
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel ring Krull Dim quot add one le 978fb20ae9e3: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilber
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel ring Krull Dim quot add one le 978fb20ae9e3 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel ring Krull Dim quot add one le 978fb20ae9e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ColonSpanSingletonEqOfNotMem.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ColonSpanSingletonEqOfNotMem.lean#L15-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ColonSpanSingletonEqOfNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_ringKrullDim_quot_add_one_le_978fb20ae9e3 {K : Type*} {ι : K → Type*} {F : Type*} [Field F]
    {P Q : Ideal (MRing ι F)} [P.IsPrime] (hPQ : P ≤ Q)
    {f : MRing ι F} (hfP : f ∉ P) (hfQ : f ∈ Q) :
    ringKrullDim (MRing ι F ⧸ Q) + 1 ≤ ringKrullDim (MRing ι F ⧸ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HilbertSamuel».«ringKrullDim_quot_add_one_le» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_ringKrullDim_quot_add_one_le_978fb20ae9e3
