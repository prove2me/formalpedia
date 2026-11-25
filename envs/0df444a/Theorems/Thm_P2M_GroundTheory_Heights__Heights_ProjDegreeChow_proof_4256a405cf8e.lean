-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjDegreeChow_proof_4256a405cf8e
-- name    : P2M_GroundTheory_Heights__Heights_ProjDegreeChow_proof_4256a405cf8e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:35:05.67398+00:00
-- url     : https://prove2.me/theorems/9a1d6655-b2da-46ea-9976-bbc962968c6c
-- title:
--   P2 M Ground Theory Heights  Heights Proj Degree Chow proof 4256a405cf8e: P2 M Ground Theory Heights  Heights Proj Degree Chow proof 4256a405cf8e
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Degree Chow proof 4256a405cf8e construction uses the P2 M Ground Theory Heights  Heights Proj Degree Chow proof 4256a405cf8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjDegreeChow.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjDegreeChow.lean#L16-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjDegreeChow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecDegreeLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecDegreeGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjDegreeChow
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

theorem P2M_GroundTheory_Heights__Heights_ProjDegreeChow_proof_4256a405cf8e (h₁ : ProjSecDegree.Statement) (h₂ : ProjSecDomain.Statement)
    (h₃ : ProjChowNonzero.Statement) (h₄ : SecDegreeLe.Statement) (h₅ : SecDegreeGe.Statement) :
    ProjDegreeChow.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjDegreeChow».«proof» := P2M_GroundTheory_Heights__Heights_ProjDegreeChow_proof_4256a405cf8e
