-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineOfLargeDegreeFromZ_proofDual_37975d7ce3cb
-- name    : P2M_GroundTheory_Heights__Heights_LineOfLargeDegreeFromZ_proofDual_37975d7ce3cb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:33:11.803894+00:00
-- url     : https://prove2.me/theorems/843e0845-74e6-5060-99d8-9f03d2e12176
-- title:
--   P2 M Ground Theory Heights  Heights Line Of Large Degree From Z proof Dual 37975d7ce3cb: P2 M Ground Theory Heights  Heights Line Of Large Degree From Z proof Dual 37975d7ce3cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Line Of Large Degree From Z proof Dual 37975d7ce3cb construction uses the P2 M Ground Theory Heights  Heights Line Of Large Degree From Z proof Dual 37975d7ce3cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLineOfLargeDegreeDual.lean#L9-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLineOfLargeDegreeDual.lean#L9-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLineOfLargeDegreeDual
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

theorem P2M_GroundTheory_Heights__Heights_LineOfLargeDegreeFromZ_proofDual_37975d7ce3cb (hBasis : DualLatticeBasisExists.Statement)
    (hBij : DualEmbBijective.Statement) (hArith : DualArithVar.Statement)
    (hSemi : DualLineSemipositive.Statement) (hNef : NefOfNonneg.Statement)
    (hConj : DualLineConj.Statement) (hPt : DualPointLineDegree.Statement)
    (hTop : DualTopBound.Statement) (hPos : DualGeomDegPos.Statement) :
    LineOfLargeDegreeFromZ.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LineOfLargeDegreeFromZ».«proofDual» := P2M_GroundTheory_Heights__Heights_LineOfLargeDegreeFromZ_proofDual_37975d7ce3cb
