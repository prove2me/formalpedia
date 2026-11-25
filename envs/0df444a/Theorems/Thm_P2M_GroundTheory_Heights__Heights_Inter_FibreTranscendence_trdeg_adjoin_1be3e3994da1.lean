-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_trdeg_adjoin_1be3e3994da1
-- name    : P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_trdeg_adjoin_1be3e3994da1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:11.0102+00:00
-- url     : https://prove2.me/theorems/06f6f387-3bbd-4e88-9489-d559369aa9d8
-- title:
--   P2 M Ground Theory Heights  Heights Inter Fibre Transcendence trdeg adjoin 1be3e3994da1: P2 M Ground Theory Heights  Heights Inter Fibre Transcendence trdeg adjoin 1be3e3994da1
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Fibre Transcendence trdeg adjoin 1be3e3994da1 construction uses the P2 M Ground Theory Heights  Heights Inter Fibre Transcendence trdeg adjoin 1be3e3994da1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AevalMemAdjoin.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AevalMemAdjoin.lean#L41-L49

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

theorem P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_trdeg_adjoin_1be3e3994da1 [Fintype K] [∀ k, Fintype (ι k)] (hE : EvalKerKrullDim.Statement) {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L]
    (y : (Σ k, ι k) → L) {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J)
    (hJ : RingHom.ker (aeval y : MRing ι →ₐ[ℤ] L) = J) {n : ℕ} (hV : IsProjVarF (J.map (PointVertical.red (ι := ι) p)) n) :
    Algebra.trdeg (ZMod p) (IntermediateField.adjoin (ZMod p) (Set.range y)) = ((n + Fintype.card K : ℕ) : Cardinal) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«FibreTranscendence».«trdeg_adjoin» := P2M_GroundTheory_Heights__Heights_Inter_FibreTranscendence_trdeg_adjoin_1be3e3994da1
