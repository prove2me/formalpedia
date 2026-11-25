-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockTrdeg_isHomogeneous_forgetWeight_72c1617be2ea
-- name    : P2M_GroundTheory_Heights__Heights_BlockTrdeg_isHomogeneous_forgetWeight_72c1617be2ea
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:16:27.334209+00:00
-- url     : https://prove2.me/theorems/a2aa4025-d22d-4a07-9b7f-6d0cbf16d3cc
-- title:
--   P2 M Ground Theory Heights  Heights Block Trdeg is Homogeneous forget Weight 72c1617be2ea: P2 M Ground Theory Heights  Heights Block Trdeg is Homogeneous forget Weight 72c1617be2ea
-- statement:
--   The P2 M Ground Theory Heights  Heights Block Trdeg is Homogeneous forget Weight 72c1617be2ea construction uses the P2 M Ground Theory Heights  Heights Block Trdeg is Homogeneous forget Weight 72c1617be2ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PBlockTrdeg.lean#L81-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PBlockTrdeg.lean#L81-L90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsBlockTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PBlockTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 Algebra Cardinal
open GroundTheory.Heights₂.Heights.BlockTrdeg
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open scoped Classical
variable {K : Type} {K' : Type} [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_BlockTrdeg_isHomogeneous_forgetWeight_72c1617be2ea (κ : K → K') {P : Ideal (MRing ι')} (h : IsMultiHomogIdeal P) :
    P.IsHomogeneous (weightedHomogeneousSubmodule ℤ (forgetWeight (ι' := ι') κ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BlockTrdeg».«isHomogeneous_forgetWeight» := P2M_GroundTheory_Heights__Heights_BlockTrdeg_isHomogeneous_forgetWeight_72c1617be2ea
