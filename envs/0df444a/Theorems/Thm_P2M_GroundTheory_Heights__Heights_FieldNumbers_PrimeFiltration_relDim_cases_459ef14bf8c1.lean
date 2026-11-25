-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_relDim_cases_459ef14bf8c1
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_relDim_cases_459ef14bf8c1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:12.777151+00:00
-- url     : https://prove2.me/theorems/b1ee4040-61c7-41d5-a732-857613d86a99
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration rel Dim cases 459ef14bf8c1: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration rel Dim cases 459ef14bf8c1
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration rel Dim cases 459ef14bf8c1 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration rel Dim cases 459ef14bf8c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L339-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L339-L375

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_relDim_cases_459ef14bf8c1 {I Q : Ideal (MRing ι F)} [hQ : Q.IsPrime] (hIQ : I ≤ Q) :
    relDim Q < relDim I ∨ (Q ∈ I.minimalPrimes ∧ relDim Q = relDim I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«relDim_cases» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_relDim_cases_459ef14bf8c1
