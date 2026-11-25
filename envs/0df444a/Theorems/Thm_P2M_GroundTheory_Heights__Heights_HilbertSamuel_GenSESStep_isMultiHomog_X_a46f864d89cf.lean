-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_isMultiHomog_X_a46f864d89cf
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_isMultiHomog_X_a46f864d89cf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:56.53548+00:00
-- url     : https://prove2.me/theorems/20321597-fa02-4bee-a49c-ccf9a529fcea
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep is Multi Homog X a46f864d89cf: P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep is Multi Homog X a46f864d89cf
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep is Multi Homog X a46f864d89cf construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep is Multi Homog X a46f864d89cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGenSESStep.lean#L26-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGenSESStep.lean#L26-L39

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_isMultiHomog_X_a46f864d89cf (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRingOver S ι) (fun l => if l = k then 1 else 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GenSESStep».«isMultiHomog_X» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_isMultiHomog_X_a46f864d89cf
