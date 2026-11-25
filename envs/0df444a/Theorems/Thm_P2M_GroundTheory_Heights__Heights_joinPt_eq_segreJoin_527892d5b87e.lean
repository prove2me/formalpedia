-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_joinPt_eq_segreJoin_527892d5b87e
-- name    : P2M_GroundTheory_Heights__Heights_joinPt_eq_segreJoin_527892d5b87e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:41:33.940435+00:00
-- url     : https://prove2.me/theorems/f9b74cb3-dba9-485c-87c8-16cf472c1b7c
-- title:
--   P2 M Ground Theory Heights  Heights join Pt eq segre Join 527892d5b87e: P2 M Ground Theory Heights  Heights join Pt eq segre Join 527892d5b87e
-- statement:
--   The P2 M Ground Theory Heights  Heights join Pt eq segre Join 527892d5b87e construction uses the P2 M Ground Theory Heights  Heights join Pt eq segre Join 527892d5b87e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L117-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L117-L118

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback
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
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type}

theorem P2M_GroundTheory_Heights__Heights_joinPt_eq_segreJoin_527892d5b87e (x : ι → Ω) (z : κ → Ω') :
    joinPt x z = segreJoin (fun i => algebraMap Ω Ω' (x i)) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«joinPt_eq_segreJoin» := P2M_GroundTheory_Heights__Heights_joinPt_eq_segreJoin_527892d5b87e
