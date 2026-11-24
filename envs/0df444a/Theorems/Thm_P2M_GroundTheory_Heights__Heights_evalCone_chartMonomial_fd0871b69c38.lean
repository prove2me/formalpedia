-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38
-- name    : P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:55.993959+00:00
-- url     : https://prove2.me/theorems/9c8e12a3-2f02-4a39-bd79-900cffd78bc0
-- title:
--   P2 M Ground Theory Heights  Heights eval Cone chart Monomial fd0871b69c38: P2 M Ground Theory Heights  Heights eval Cone chart Monomial fd0871b69c38
-- statement:
--   The P2 M Ground Theory Heights  Heights eval Cone chart Monomial fd0871b69c38 construction uses the P2 M Ground Theory Heights  Heights eval Cone chart Monomial fd0871b69c38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Statements.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Statements.lean#L67-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38 {F : Type*} [CommRing F] (z : Cone n F)
    (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    evalCone z (chartMonomial c d) = ∏ k, z k (c k) ^ d k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«evalCone_chartMonomial» := P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38
