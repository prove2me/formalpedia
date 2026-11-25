-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionNorm_evalCone_chartMonomial_ae75ba626c28
-- name    : P2M_GroundTheory_Heights__Heights_SectionNorm_evalCone_chartMonomial_ae75ba626c28
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:38:32.147306+00:00
-- url     : https://prove2.me/theorems/74cf9bfa-3e52-5051-b55a-81223c20e6f1
-- title:
--   P2 M Ground Theory Heights  Heights Section Norm eval Cone chart Monomial ae75ba626c28: P2 M Ground Theory Heights  Heights Section Norm eval Cone chart Monomial ae75ba626c28
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Norm eval Cone chart Monomial ae75ba626c28 construction uses the P2 M Ground Theory Heights  Heights Section Norm eval Cone chart Monomial ae75ba626c28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomial.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomial.lean#L17-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionNorm
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_SectionNorm_evalCone_chartMonomial_ae75ba626c28 (z : Cone n ℂ) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    evalCone z (chartMonomial c d) = ∏ k, z k (c k) ^ d k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionNorm».«evalCone_chartMonomial» := P2M_GroundTheory_Heights__Heights_SectionNorm_evalCone_chartMonomial_ae75ba626c28
