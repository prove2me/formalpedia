-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineIndexNeZero_proof_a8fe4bc038ad
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineIndexNeZero_proof_a8fe4bc038ad
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:47:43.831335+00:00
-- url     : https://prove2.me/theorems/de452196-97ef-497f-bbd0-5ff480ca9573
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Line Index Ne Zero proof a8fe4bc038ad: P2 M Ground Theory Heights  Heights Finite Covolume Line Index Ne Zero proof a8fe4bc038ad
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Line Index Ne Zero proof a8fe4bc038ad construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Line Index Ne Zero proof a8fe4bc038ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineIndexNeZero.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineIndexNeZero.lean#L9-L11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PVectorOrbitsFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineIndexNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceUnitsFiniteIndex_proof_eec00df32b44
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_VectorOrbitsFinite_proof_a256cbf4870a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineIndexNeZero_proof_a8fe4bc038ad (E W : Type*) [Field E] [NumberField E] [AddCommGroup W]
    [Module E W] : LineIndexNeZero.Statement E W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«LineIndexNeZero».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineIndexNeZero_proof_a8fe4bc038ad
