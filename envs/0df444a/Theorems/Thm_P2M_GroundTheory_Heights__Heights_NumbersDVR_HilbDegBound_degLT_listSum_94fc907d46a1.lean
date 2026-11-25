-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_degLT_listSum_94fc907d46a1
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_degLT_listSum_94fc907d46a1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:59.884459+00:00
-- url     : https://prove2.me/theorems/1429a9da-9ded-4106-8a2a-ad74cf9c9e3e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound deg LT list Sum 94fc907d46a1: P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound deg LT list Sum 94fc907d46a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound deg LT list Sum 94fc907d46a1 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound deg LT list Sum 94fc907d46a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHilbDegBound.lean#L80-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHilbDegBound.lean#L80-L93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHilbDegBound
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
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.HilbDegBound
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_degLT_listSum_94fc907d46a1 (h6 : DegLTClosure.Statement) {α : Type*} (n : ℕ)
    (g : α → (K → ℤ) → ℤ) (l : List α) (hl : ∀ a ∈ l, DegLT (g a) n) :
    DegLT (fun m => (l.map fun a => g a m).sum) n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HilbDegBound».«degLT_listSum» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_degLT_listSum_94fc907d46a1
