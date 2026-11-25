-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussPoissonBound_proof_dfde059c4be9
-- name    : P2M_GroundTheory_Heights__Heights_GaussPoissonBound_proof_dfde059c4be9
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:26.933838+00:00
-- url     : https://prove2.me/theorems/87521546-4985-4da7-aa7a-255c740cb381
-- title:
--   P2 M Ground Theory Heights  Heights Gauss Poisson Bound proof dfde059c4be9: P2 M Ground Theory Heights  Heights Gauss Poisson Bound proof dfde059c4be9
-- statement:
--   The P2 M Ground Theory Heights  Heights Gauss Poisson Bound proof dfde059c4be9 construction uses the P2 M Ground Theory Heights  Heights Gauss Poisson Bound proof dfde059c4be9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussPoissonBound.lean#L24-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussPoissonBound.lean#L24-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussPoissonBound
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
open Matrix Real MeasureTheory
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open PGaussPoissonBound

theorem P2M_GroundTheory_Heights__Heights_GaussPoissonBound_proof_dfde059c4be9 (hL : GaussLatticeIsLattice.Statement)
    (hV : GaussLatticeCovolume.Statement) (hK : GaussLatticeCoords.Statement)
    (hF : GaussFourierSelf.Statement) : GaussPoissonBound.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GaussPoissonBound».«proof» := P2M_GroundTheory_Heights__Heights_GaussPoissonBound_proof_dfde059c4be9
