-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_proof_3e1de966b9e3
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_proof_3e1de966b9e3
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:16:18.557531+00:00
-- url     : https://prove2.me/theorems/b4fe76bc-c349-49be-b8a8-d29eff4857e2
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep proof 3e1de966b9e3: P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep proof 3e1de966b9e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep proof 3e1de966b9e3 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep proof 3e1de966b9e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGenSESStep.lean#L149-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGenSESStep.lean#L149-L238

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGenSESStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_proof_3e1de966b9e3 (hSES : KH.CechSESStatement) (hMap : KH.CechMapDegStatement) : GenSESStep.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GenSESStep».«proof» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_proof_3e1de966b9e3
