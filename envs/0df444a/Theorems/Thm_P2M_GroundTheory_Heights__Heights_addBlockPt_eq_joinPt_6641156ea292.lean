-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_addBlockPt_eq_joinPt_6641156ea292
-- name    : P2M_GroundTheory_Heights__Heights_addBlockPt_eq_joinPt_6641156ea292
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:40:58.299659+00:00
-- url     : https://prove2.me/theorems/cd309004-acc4-4529-b7d8-0a048cbb101c
-- title:
--   P2 M Ground Theory Heights  Heights add Block Pt eq join Pt 6641156ea292: P2 M Ground Theory Heights  Heights add Block Pt eq join Pt 6641156ea292
-- statement:
--   The P2 M Ground Theory Heights  Heights add Block Pt eq join Pt 6641156ea292 construction uses the P2 M Ground Theory Heights  Heights add Block Pt eq join Pt 6641156ea292 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L160-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AddBlockPullbackOfChartBundlePullback.lean#L160-L166

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
variable {K : Type} {ι : K → Type} {κ : Type}

theorem P2M_GroundTheory_Heights__Heights_addBlockPt_eq_joinPt_6641156ea292 {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω']
    (y : (Σ k, ι k) → Ω) (z : κ → Ω') :
    addBlockPt (Ω := Ω) (Ω' := Ω') y z =
      IndefiniteRowSideFullHecke.Antisym.joinPt (fun q => algebraMap Ω Ω' (y q))
        (fun q : (Σ _ : Unit, κ) => z q.2) ∘ addBlockIdxEquiv := by sorry

alias «GroundTheory».«Heights₂».«Heights».«addBlockPt_eq_joinPt» := P2M_GroundTheory_Heights__Heights_addBlockPt_eq_joinPt_6641156ea292
