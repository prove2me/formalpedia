-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_latticePoint_978f926e6c9b
-- name    : P2M_GroundTheory_Heights__Heights_sum_latticePoint_978f926e6c9b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:29.643266+00:00
-- url     : https://prove2.me/theorems/ab4c6deb-20fa-461a-bbb8-b2f2b1f47a10
-- title:
--   P2 M Ground Theory Heights  Heights sum lattice Point 978f926e6c9b: P2 M Ground Theory Heights  Heights sum lattice Point 978f926e6c9b
-- statement:
--   The P2 M Ground Theory Heights  Heights sum lattice Point 978f926e6c9b construction uses the P2 M Ground Theory Heights  Heights sum lattice Point 978f926e6c9b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L57-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L57-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
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
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_sum_latticePoint_978f926e6c9b {φ : Fin (N + 1) → Fin (r + 1) → K} (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ)
    {D : ℤ} {c : Fin (N + 1) → ℤ} {v : Fin (r + 1) → K} (hc : ∑ b, c b • φ b = D • v) :
    ∑ b, (c b : ℂ) * latticePoint φ σ w () b = D * ∑ j, σ (v j) * w j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sum_latticePoint» := P2M_GroundTheory_Heights__Heights_sum_latticePoint_978f926e6c9b
