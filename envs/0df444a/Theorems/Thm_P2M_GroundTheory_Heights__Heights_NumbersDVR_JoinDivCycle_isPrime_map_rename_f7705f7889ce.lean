-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_isPrime_map_rename_f7705f7889ce
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_isPrime_map_rename_f7705f7889ce
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:04:13.207949+00:00
-- url     : https://prove2.me/theorems/36f8e83a-a1bb-4475-a6b3-d2b3e3e975a2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle is Prime map rename f7705f7889ce: P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle is Prime map rename f7705f7889ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle is Prime map rename f7705f7889ce construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle is Prime map rename f7705f7889ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinDivCycle.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinDivCycle.lean#L82-L84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinDivCycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinDivCycle
variable {R : Type} [CommRing R] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
local notation "ψ" => joinPolyEquiv (R := R) (ι := ι)
local notation "ε" => rename (R := R) (liftVar (ι := ι) ptIdx)

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_isPrime_map_rename_f7705f7889ce (Q : Ideal (MRing ι R)) [Q.IsPrime] : (Q.map ε).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinDivCycle».«isPrime_map_rename» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_isPrime_map_rename_f7705f7889ce
