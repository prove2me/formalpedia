-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GreenFromLelong_proof_0fe43a25b4c2
-- name    : P2M_GroundTheory_Heights__Heights_GreenFromLelong_proof_0fe43a25b4c2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:15:26.365097+00:00
-- url     : https://prove2.me/theorems/b67c020c-ffb5-5752-8845-c7c4610ac805
-- title:
--   P2 M Ground Theory Heights  Heights Green From Lelong proof 0fe43a25b4c2: P2 M Ground Theory Heights  Heights Green From Lelong proof 0fe43a25b4c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Green From Lelong proof 0fe43a25b4c2 construction uses the P2 M Ground Theory Heights  Heights Green From Lelong proof 0fe43a25b4c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGreenFromLelong.lean#L13-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGreenFromLelong.lean#L13-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_MonotoneDoubleLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDivCyclePrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowFormSectionAlgClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGreenFromLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DivCyclePrime_proof_a79e8cf92f7f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProperSymm_proof_b0183563c887

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
open MvPolynomial MeasureTheory Filter Topology

theorem P2M_GroundTheory_Heights__Heights_GreenFromLelong_proof_0fe43a25b4c2 (hS : FormIntSymm.Statement) (hP : FormIntPos.Statement)
    (hL : FormIntLelong.Statement) (hD : RegConeLimit.Statement)
    (hCh : ChowFormSectionAlgClosed.Statement) : GreenFromLelong.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GreenFromLelong».«proof» := P2M_GroundTheory_Heights__Heights_GreenFromLelong_proof_0fe43a25b4c2
