-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_expand_29cfce2fc705
-- name    : P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_expand_29cfce2fc705
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:48:23.839416+00:00
-- url     : https://prove2.me/theorems/21f6bb61-d9e4-5044-9a56-6e0d836f2469
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Log Pow mdisc expand 29cfce2fc705: P2 M Ground Theory Heights  Heights Ma Dens Log Pow mdisc expand 29cfce2fc705
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Log Pow mdisc expand 29cfce2fc705 construction uses the P2 M Ground Theory Heights  Heights Ma Dens Log Pow mdisc expand 29cfce2fc705 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLogPow.lean#L44-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLogPow.lean#L44-L88

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLogPow
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
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLogPow
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_expand_29cfce2fc705 (α β : ℂ) (H G : Matrix (Fin D) (Fin D) ℂ)
    (hG : ∀ (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (i j : Fin D), i ≠ j → A i = G → A j = G →
      mdisc A = 0) :
    ∀ (s : Finset (Fin D)) (C : Fin D → Matrix (Fin D) (Fin D) ℂ), (∀ i ∈ s, C i = H) →
      mdisc (fun i => if i ∈ s then α • H + β • G else C i) =
        α ^ s.card * mdisc C + α ^ (s.card - 1) * β * ∑ i ∈ s, mdisc (Function.update C i G) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensLogPow».«mdisc_expand» := P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_expand_29cfce2fc705
