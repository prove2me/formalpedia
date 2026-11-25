-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_ker_aeval_F_7dc16d4c0989
-- name    : P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_ker_aeval_F_7dc16d4c0989
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:26:33.2249+00:00
-- url     : https://prove2.me/theorems/6dbdee7a-5916-46c9-bacd-120883dd3de8
-- title:
--   P2 M Ground Theory Heights  Heights Inter Fibre Transcendence ker aeval F 7dc16d4c0989: P2 M Ground Theory Heights  Heights Inter Fibre Transcendence ker aeval F 7dc16d4c0989
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Fibre Transcendence ker aeval F 7dc16d4c0989 construction uses the P2 M Ground Theory Heights  Heights Inter Fibre Transcendence ker aeval F 7dc16d4c0989 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AevalMemAdjoin.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AevalMemAdjoin.lean#L33-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsEvalKerKrullDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiProjPrimeImageZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AevalMemAdjoin
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.FibreTranscendence
variable {K : Type} {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_ker_aeval_F_7dc16d4c0989 {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] (y : (Σ k, ι k) → L)
    {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) (hJ : RingHom.ker (aeval y : MRing ι →ₐ[ℤ] L) = J) :
    RingHom.ker (aeval y : MRingOver (ZMod p) ι →ₐ[ZMod p] L) = J.map (PointVertical.red (ι := ι) p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«FibreTranscendence».«ker_aeval_F» := P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_ker_aeval_F_7dc16d4c0989
