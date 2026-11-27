-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassHeightBound_proof_cec452e5a7c6
-- name    : P2M_GroundTheory_Heights__Heights_GrassHeightBound_proof_cec452e5a7c6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:13:42.695164+00:00
-- url     : https://prove2.me/theorems/be34b086-5d0b-4455-b458-e452607fe7ad
-- title:
--   P2 M Ground Theory Heights  Heights Grass Height Bound proof cec452e5a7c6: P2 M Ground Theory Heights  Heights Grass Height Bound proof cec452e5a7c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Grass Height Bound proof cec452e5a7c6 construction uses the P2 M Ground Theory Heights  Heights Grass Height Bound proof cec452e5a7c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassHeightBound.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassHeightBound.lean#L9-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassHeightBound
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
open ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_GrassHeightBound_proof_cec452e5a7c6 (hArith : GrassArithVar.Statement) (hRoot : RootArithVar.Statement)
    (hSemi : FsLineSemipositive.Statement) (hNef : NefOfNonneg.Statement)
    (hConj : FsConjInvariant.Statement) (hLe : GrassLeRoot.Statement) (hHt : RootHeight.Statement)
    (hDense : RootDense.Statement) : GrassHeightBound.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassHeightBound».«proof» := P2M_GroundTheory_Heights__Heights_GrassHeightBound_proof_cec452e5a7c6
