-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_mkF_X_ne_zero_5ca902d68882
-- name    : P2M_GroundTheory_Heights__Heights_SmallSections_mkF_X_ne_zero_5ca902d68882
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:07.114571+00:00
-- url     : https://prove2.me/theorems/fc10a846-8c5c-4fd5-aed7-079f94ce7e25
-- title:
--   P2 M Ground Theory Heights  Heights Small Sections mk F X ne zero 5ca902d68882: P2 M Ground Theory Heights  Heights Small Sections mk F X ne zero 5ca902d68882
-- statement:
--   The P2 M Ground Theory Heights  Heights Small Sections mk F X ne zero 5ca902d68882 construction uses the P2 M Ground Theory Heights  Heights Small Sections mk F X ne zero 5ca902d68882 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L66-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_SmallSections_mkF_X_ne_zero_5ca902d68882 {P : ArithVariety n} {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (k : ι) :
    P.mkF (X ⟨k, c k⟩) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SmallSections».«mkF_X_ne_zero» := P2M_GroundTheory_Heights__Heights_SmallSections_mkF_X_ne_zero_5ca902d68882
