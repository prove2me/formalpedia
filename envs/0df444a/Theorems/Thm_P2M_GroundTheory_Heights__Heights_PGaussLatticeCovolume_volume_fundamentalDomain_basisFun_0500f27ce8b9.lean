-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_volume_fundamentalDomain_basisFun_0500f27ce8b9
-- name    : P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_volume_fundamentalDomain_basisFun_0500f27ce8b9
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:36.437856+00:00
-- url     : https://prove2.me/theorems/efce1102-4803-465d-aba3-6d65f5979a24
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Lattice Covolume volume fundamental Domain basis Fun 0500f27ce8b9: P2 M Ground Theory Heights  Heights PGauss Lattice Covolume volume fundamental Domain basi
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Lattice Covolume volume fundamental Domain basis Fun 0500f27ce8b9 construction uses the P2 M Ground Theory Heights  Heights PGauss Lattice Covolume volume fundamental Domain basis Fun 0500f27ce8b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussLatticeCovolume.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussLatticeCovolume.lean#L54-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussLatticeCovolume
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
open Matrix MeasureTheory Module
noncomputable section
open GroundTheory.Heights₂.Heights.PGaussLatticeCovolume

theorem P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_volume_fundamentalDomain_basisFun_0500f27ce8b9 (g : ℕ) :
    volume.real (ZSpan.fundamentalDomain (EuclideanSpace.basisFun (Fin g) ℝ).toBasis) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussLatticeCovolume».«volume_fundamentalDomain_basisFun» := P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_volume_fundamentalDomain_basisFun_0500f27ce8b9
